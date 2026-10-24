-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:46:14.155304+00:00
-- url     : https://prove2.me/submissions/a60d41f5-6c41-4a2b-bc21-40b09de221ce

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_mul_sub_408915f
import Theorems.Thm_FunctionalInequalities_L2_integral_affine_sq_408915f
import Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_408915f

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
/-- **Pythagoras for the affine decomposition** of `f ∈ L²(μ)`. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ =
      (∫ x, f x ∂μ) ^ 2 + ∑ j, (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
        ∫ x, FunctionalInequalities.L2.affineOrthPart μ f x ^ 2 ∂μ := by
    let h := FunctionalInequalities.L2.affineOrthPart μ f
    let c := ∫ y, f y ∂μ
    let a : Fin n → ℝ := fun j =>
      ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ
    let P : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
      c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫

    have hdecomp : ∀ x, f x = h x + P x := by
      intro x
      simp only [h, P, c, a, FunctionalInequalities.L2.affineOrthPart]
      ring

    have hh : MemLp h 2 μ := by
      simpa [h] using (FunctionalInequalities.L2.memLp_affineOrthPart_408915f μ hμ2 hf)

    have hPfun : P = fun x => f x - h x := by
      funext x
      linarith [hdecomp x]

    have hP : MemLp P 2 μ := by
      rw [hPfun]
      exact hf.sub hh

    have hh_sq : Integrable (fun x => h x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).1 hh

    have hP_sq : Integrable (fun x => P x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).1 hP

    have hprod : Integrable (fun x => h x * P x) μ :=
      MemLp.integrable_mul hh hP

    have hcross0 : (∫ x, h x * (f x - h x) ∂μ) = 0 := by
      simpa [h] using
        (FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_408915f μ hμ2 hμ0 hμcov hf)

    have hcross : (∫ x, h x * P x ∂μ) = 0 := by
      calc
        (∫ x, h x * P x ∂μ) =
            ∫ x, h x * (f x - h x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hPfun]
        _ = 0 := hcross0

    have hPsq : (∫ x, P x ^ 2 ∂μ) = c ^ 2 + ∑ j, a j ^ 2 := by
      simpa [P] using
        (FunctionalInequalities.L2.integral_affine_sq_408915f μ hμ2 hμ0 hμcov c a)

    have hsum :
        Integrable (fun x => h x ^ 2 + 2 * (h x * P x)) μ :=
      hh_sq.add (hprod.const_mul 2)

    have hsq :
        (∫ x, f x ^ 2 ∂μ) =
          (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
            ∫ x, P x ^ 2 ∂μ := by
      calc
        (∫ x, f x ^ 2 ∂μ) =
            ∫ x, (h x + P x) ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hdecomp x]
        _ = ∫ x, (h x ^ 2 + 2 * (h x * P x) + P x ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
        _ = (∫ x, h x ^ 2 + 2 * (h x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ := integral_add hsum hP_sq
        _ = ((∫ x, h x ^ 2 ∂μ) +
              ∫ x, 2 * (h x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
              rw [integral_add hh_sq (hprod.const_mul 2)]
        _ = (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
              rw [integral_const_mul]

    calc
      (∫ x, f x ^ 2 ∂μ) =
          (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
            ∫ x, P x ^ 2 ∂μ := hsq
      _ = (∫ x, h x ^ 2 ∂μ) + (c ^ 2 + ∑ j, a j ^ 2) := by
        rw [hcross, hPsq]
        ring
      _ = (∫ x, f x ∂μ) ^ 2 +
            ∑ j, (∫ x,
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
            ∫ x, FunctionalInequalities.L2.affineOrthPart μ f x ^ 2 ∂μ := by
        simp only [h, c, a]
        ring
