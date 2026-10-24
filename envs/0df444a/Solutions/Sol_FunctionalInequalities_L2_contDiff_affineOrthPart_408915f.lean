-- Prove2me | solution 1 for FunctionalInequalities.L2.contDiff_affineOrthPart_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:00:59.911685+00:00
-- url     : https://prove2.me/submissions/4d8783cb-2c14-4a9f-88c2-1e83c4dd8a5d

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities.L2 in
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
