-- Prove2me | solution 1 for ContinuousLinearMap.isPositive_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:32.863846+00:00
-- url     : https://prove2.me/submissions/624a228a-b671-461a-ae2a-83c19317a911

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveIntegral

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
universe u v
open ContinuousLinearMap
variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace ContinuousLinearMap
theorem _root_.solution (f : X → E →L[ℂ] E) (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, IsPositive (f x)) : IsPositive (∫ x, f x ∂μ) := by
  rw [isPositive_iff_complex]
  intro v
  have hfv : Integrable (fun x => f x v) μ :=
    (ContinuousLinearMap.apply ℂ E v).integrable_comp hf
  have hinner : Integrable (fun x => ⟪f x v, v⟫_ℂ) μ := hfv.inner_const v
  have hinter :
      ⟪(∫ x, f x ∂μ) v, v⟫_ℂ = ∫ x, ⟪f x v, v⟫_ℂ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hf]
    calc
      ⟪∫ x, f x v ∂μ, v⟫_ℂ = starRingEnd ℂ ⟪v, ∫ x, f x v ∂μ⟫_ℂ :=
        (inner_conj_symm (𝕜 := ℂ) (∫ x, f x v ∂μ) v).symm
      _ = starRingEnd ℂ (∫ x, ⟪v, f x v⟫_ℂ ∂μ) := by rw [integral_inner hfv]
      _ = ∫ x, starRingEnd ℂ ⟪v, f x v⟫_ℂ ∂μ := integral_conj.symm
      _ = ∫ x, ⟪f x v, v⟫_ℂ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact inner_conj_symm (𝕜 := ℂ) (f x v) v
  constructor
  · rw [hinter, ← integral_re hinner, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    exact (isPositive_iff_complex (f x)).mp hx v |>.1
  · rw [hinter, ← integral_re hinner]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact (isPositive_iff_complex (f x)).mp hx v |>.2
end ContinuousLinearMap
