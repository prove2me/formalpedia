-- Prove2me | solution 1 for FunctionalInequalities.L2.contDiff_affineOrthPart_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:07.947855+00:00
-- url     : https://prove2.me/submissions/8661985e-b3c9-4c0d-858b-98fad80836d4

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- The affine-orthogonal part of a `C²` function is `C²` with the same second derivative. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (FunctionalInequalities.L2.affineOrthPart μ g) ∧
      ∀ x, fderiv ℝ (fderiv ℝ (FunctionalInequalities.L2.affineOrthPart μ g)) x = fderiv ℝ (fderiv ℝ g) x := by
    let e : Fin n → EuclideanSpace ℝ (Fin n) :=
      EuclideanSpace.basisFun (Fin n) ℝ
    let c : ℝ := ∫ y, g y ∂μ
    let a : Fin n → ℝ := fun j => ∫ y, ⟪e j, y⟫ * g y ∂μ
    let S : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun y => ∑ j, a j * ⟪e j, y⟫
    let C : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ∑ j, a j • innerSL ℝ (e j)
    have hrepr :
        FunctionalInequalities.L2.affineOrthPart μ g = fun y => g y - c - S y := by
      funext y
      simp only [FunctionalInequalities.L2.affineOrthPart, c, a, S, e]
    have hlin (j : Fin n) :
        ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ⟪e j, y⟫) := by
      have heq :
          (fun y : EuclideanSpace ℝ (Fin n) => ⟪e j, y⟫) =
            innerSL ℝ (e j) := by
        funext y
        simp only [innerSL_apply_apply]
      rw [heq]
      exact (innerSL ℝ (e j)).contDiff
    have hS : ContDiff ℝ 2 S := by
      exact
        ContDiff.sum fun j _ =>
          (contDiff_const :
            ContDiff ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => a j)).mul (hlin j)
    have hcont : ContDiff ℝ 2 (fun y => g y - c - S y) :=
      (hg.sub contDiff_const).sub hS
    have hSd (y : EuclideanSpace ℝ (Fin n)) : HasFDerivAt S C y := by
      have h :=
        HasFDerivAt.sum (u := Finset.univ)
          (fun j _ =>
            ((innerSL ℝ (e j)).hasFDerivAt (x := y)).const_mul (a j))
      have hsum :
          (∑ j : Fin n, fun z => a j * ⟪e j, z⟫) =
            (fun z => ∑ j : Fin n, a j * ⟪e j, z⟫) := by
        funext z
        simp only [Finset.sum_apply]
      change
        HasFDerivAt
          (fun z => ∑ j : Fin n, a j * ⟪e j, z⟫)
          (∑ j : Fin n, a j • innerSL ℝ (e j)) y
      rw [← hsum]
      simpa only [innerSL_apply_apply] using h
    have hfirst (y : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun z => g z - c - S z) y = fderiv ℝ g y - C := by
      have hg' : HasFDerivAt g (fderiv ℝ g y) y :=
        (hg.differentiable (by norm_num) y).hasFDerivAt
      exact ((hg'.sub_const c).sub (hSd y)).fderiv
    have hf :
        fderiv ℝ (FunctionalInequalities.L2.affineOrthPart μ g) = fun y => fderiv ℝ g y - C := by
      rw [hrepr]
      funext y
      exact hfirst y
    constructor
    · rw [hrepr]
      exact hcont
    · intro x
      rw [hf, fderiv_sub_const]
