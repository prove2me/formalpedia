-- Prove2me | solution 1 for FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:07.347665+00:00
-- url     : https://prove2.me/submissions/b6ac13a0-df0a-4b39-a2ca-b3015ad220a8

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
/-- The total coordinate Hessian is bounded by the gradient Lipschitz constant;
this does not assert C2 regularity or classical differentiability everywhere. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ ≤ (G : ℝ) := by
  let L := fderiv ℝ (gradient u) x
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let T := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
  rw [FunctionalInequalities.Probability.Stein.n10_hessian]
  change ‖T (L (e i)) (e j)‖ ≤ (G : ℝ)
  calc
    ‖T (L (e i)) (e j)‖ ≤ ‖T (L (e i))‖ * ‖e j‖ :=
      (T (L (e i))).le_opNorm (e j)
    _ = ‖L (e i)‖ := by
      rw [T.norm_map, e.norm_eq_one j, mul_one]
    _ ≤ ‖L‖ * ‖e i‖ := L.le_opNorm (e i)
    _ = ‖L‖ := by
      rw [e.norm_eq_one i, mul_one]
    _ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hG
