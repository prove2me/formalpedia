-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a530_positive_value_integrable_of_exponential_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:27:56.130862+00:00
-- url     : https://prove2.me/submissions/a628fe8f-453c-48f1-93d8-6289a0f026a0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (Z : Ω → ℝ) (θ K : ℝ)
    (hK : 0 ≤ K) (h0 : w 0 ≤ K)
    (hupper : ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (w (Z ω)) (0 : ℝ)) P) :
    Integrable (fun ω => max (w (Z ω)) (0 : ℝ)) P := by
  have hdom : Integrable (fun ω => K * Real.exp (θ * Z ω)) P :=
    hExp.const_mul K
  apply hdom.mono' hMeas
  filter_upwards [hZ] with ω hz
  have hp : 0 ≤ K * Real.exp (θ * Z ω) :=
    mul_nonneg hK (Real.exp_pos _).le
  have hw : w (Z ω) ≤ K * Real.exp (θ * Z ω) := by
    by_cases hzpos : 0 < Z ω
    · exact hupper (Z ω) hzpos
    · have hz0 : Z ω = 0 := le_antisymm (le_of_not_gt hzpos) hz
      simpa [hz0] using h0
  have hm : 0 ≤ max (w (Z ω)) (0 : ℝ) := le_max_right _ _
  simpa [Real.norm_eq_abs, abs_of_nonneg hm, abs_of_nonneg hp] using
    (max_le hw hp)
