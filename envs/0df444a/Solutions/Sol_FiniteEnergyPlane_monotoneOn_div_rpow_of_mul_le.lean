-- Prove2me | solution 1 for FiniteEnergyPlane.monotoneOn_div_rpow_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T23:01:44.656464+00:00
-- url     : https://prove2.me/submissions/e79faf4f-84e8-4b30-ac1e-7b4e2894b293

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Let `I` be differentiable on `(0, S)` with `α I(s) ≤ s I'(s)` there. Then `s ↦ I(s) / s^α` is
nondecreasing on `(0, S)`. -/
theorem monotoneOn_div_rpow_of_mul_le_aux {I I' : ℝ → ℝ} {α S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, α * I s ≤ s * I' s) :
    MonotoneOn (fun s => I s / s ^ α) (Ioo 0 S) := by
  have hd : ∀ s ∈ Ioo 0 S, HasDerivAt (fun s => I s / s ^ α)
      ((I' s * s ^ α - I s * (α * s ^ (α - 1))) / (s ^ α) ^ 2) s := by
    intro s hs
    have hp : HasDerivAt (fun x : ℝ => x ^ α) (α * s ^ (α - 1)) s :=
      Real.hasDerivAt_rpow_const (Or.inl hs.1.ne')
    exact (hI s hs).div hp (Real.rpow_pos_of_pos hs.1 α).ne'
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 S)
    (f' := fun s => (I' s * s ^ α - I s * (α * s ^ (α - 1))) / (s ^ α) ^ 2) ?_ ?_ ?_
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    exact (hd s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    have hs0 : 0 < s := hs.1
    apply div_nonneg _ (by positivity)
    have h := hineq s hs
    have hsm : s ^ (α - 1) = s ^ α / s := by
      rw [Real.rpow_sub hs0, Real.rpow_one]
    have hpos : 0 < s ^ (α - 1) := Real.rpow_pos_of_pos hs0 _
    have key : I' s * s ^ α - I s * (α * s ^ (α - 1)) = s ^ (α - 1) * (s * I' s - α * I s) := by
      rw [hsm]; field_simp
    rw [key]
    exact mul_nonneg hpos.le (by linarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution {I I' : ℝ → ℝ} {α S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, α * I s ≤ s * I' s) :
    MonotoneOn (fun s => I s / s ^ α) (Ioo 0 S) :=
  monotoneOn_div_rpow_of_mul_le_aux hI hineq
