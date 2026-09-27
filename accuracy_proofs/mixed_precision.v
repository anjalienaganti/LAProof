From LAProof.accuracy_proofs Require Import
  preamble
  common
  dotprod_model
  sum_model
  float_acc_lems
  dot_acc_lemmas.

Require Import Reals.
Require Import Coq.micromega.Lia.

Open Scope R.

Section MixedPrec.

Context {NAN : FPCore.Nans} {t_low t_high : type}.

Variables (x y : ftype t_low).

Definition emin (t : type) : Z := -femax t + 1.

Print emin.
Print fprec.
Print femax.
Print SpecFloat.emin.

Lemma dotprod_mixed_precision :
  (fprec t_high > 2 * fprec t_low)%Z /\ 
  ((1 + emin t_low - fprec t_high)%Z > emin t_high)%Z ->
  FT2R (BMULT (cast t_high x) (cast t_high y)) = (FT2R x) * (FT2R y).
Proof.
  (* Add comments to outline the main steps of the proof so it's easier to understand *)
  intros [H1 H2].
  assert (Hfinite : Binary.is_finite (BMULT (cast t_high x) (cast t_high y)) = true) by admit.
  destruct (BMULT_correct (cast t_high x) (cast t_high y) Hfinite) as [_ Hround].
  rewrite Hround.
  assert (Hx_cast : FT2R (cast t_high x) = FT2R x) by admit.
  assert (Hy_cast : FT2R (cast t_high y) = FT2R y) by admit.
  rewrite Hx_cast.
  rewrite Hy_cast.
  apply Generic_fmt.round_generic.
  apply Generic_fmt.valid_rnd_N.
  assert (Hx : Generic_fmt.generic_format Zaux.radix2 
  (SpecFloat.fexp (fprec t_low) (femax t_low)) (FT2R x)).
  unfold FT2R.
  apply Binary.generic_format_B2R.
  assert (Hy : Generic_fmt.generic_format Zaux.radix2 
  (SpecFloat.fexp (fprec t_low) (femax t_low)) (FT2R y)).
  unfold FT2R.
  apply Binary.generic_format_B2R.
  apply FLT.generic_format_FLT.
  apply FLT.FLT_format_generic in Hx.
  apply FLT.FLT_format_generic in Hy.
  destruct Hx as [fx Hx_eq Hx_bound Hx_exp].
  destruct Hy as [fy Hy_eq Hy_bound Hy_exp].
  apply (FLT.FLT_spec _ _ _ _
    {| Defs.Fnum := Defs.Fnum fx * Defs.Fnum fy;
       Defs.Fexp := Defs.Fexp fx + Defs.Fexp fy |}).
  - rewrite Hx_eq. rewrite Hy_eq.
    unfold Defs.F2R. simpl.
    rewrite bpow_plus. rewrite mult_IZR.
    ring.
  - simpl. rewrite Z.abs_mul.
    admit. (* mantissa bound using H1 *)
  - simpl.
    unfold SpecFloat.emin in Hx_exp, Hy_exp.
    unfold SpecFloat.emin.
    unfold emin in H2.
    pose proof (ZLT_elim _ _ (fprec_lt_femax_bool t_low)) as Hlt_low.
    assert (H2' :
      (femax t_low + fprec t_high <= femax t_high)%Z).
    {
      lia.
    }
    assert (H1' :
      (2 * fprec t_low + 1 <= fprec t_high)%Z).
    {
      lia.
    }
    assert (Hsum :
      (6 - 2 * femax t_low - 2 * fprec t_low
       <= Defs.Fexp fx + Defs.Fexp fy)%Z).
    {
      lia.
    }
    lia.
  - apply fprec_gt_0.
  - apply fprec_gt_0.
Admitted.

End MixedPrec.
