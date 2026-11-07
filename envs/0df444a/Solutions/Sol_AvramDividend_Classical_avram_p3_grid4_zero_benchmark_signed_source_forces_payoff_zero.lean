-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:08:32.935015+00:00
-- url     : https://prove2.me/submissions/a92c5053-7a7d-4148-96a2-327e27c7abd7

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- A nonnegative original strict payoff bounded by an integrable signed
source with nonpositive mean must vanish on the zero-value branch. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y E : Ω → ℝ)
    (hYpos : 0 ≤ᵐ[P] Y)
    (hEint : Integrable E P)
    (hEmean : (∫ ω, E ω ∂P) ≤ 0)
    (hYle : ∀ᵐ ω ∂P, Y ω ≤ E ω) :
    ∀ᵐ ω ∂P, Y ω = 0 := by
  have hEpos : 0 ≤ᵐ[P] E := by
    filter_upwards [hYpos, hYle] with ω hY hLE
    exact le_trans hY hLE
  have hZero : (∫ ω, E ω ∂P) = 0 :=
    le_antisymm hEmean (integral_nonneg_of_ae hEpos)
  have hEzero : ∀ᵐ ω ∂P, E ω = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hEpos hEint).mp hZero
  filter_upwards [hYpos, hYle, hEzero] with ω hY hLE hZ
  have hY0 : (0 : ℝ) ≤ Y ω := by simpa using hY
  have hYupper : Y ω ≤ 0 := by simpa only [hZ] using hLE
  exact le_antisymm hYupper hY0
