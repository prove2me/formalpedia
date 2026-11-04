-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_BV_small_negative_compensator_drift_physical_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:37:11.054624+00:00
-- url     : https://prove2.me/submissions/84e58cc9-1a06-467d-82c7-91c52eeaa069

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

/-- Genuine physical-clock L1 follows from original BV first-order source
domination, provided the controlled source drift is a.e. measurable. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b)) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = ∫ z in Ioo (-1 : ℝ) 0,
      (if p ∈ E ∧ p.1 ≤ τ p.2 then
        Real.exp (-(q * (p.1 : ℝ))) *
          (w (Upre p + z) - w (Upre p)) else 0) ∂X.ν)
    (hMeas : AEStronglyMeasurable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P) ∧
    Integrable (fun ω => (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal))) P := by
  let clock : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  letI : IsFiniteMeasure clock :=
    ⟨avram_p3_b_bvjump_original_physical_clock_total_mass_finite T⟩
  let C : ℝ := (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν)
  have hBound : ∀ p, |F p| ≤ |C| := by
    intro p
    rw [hF p]
    by_cases hp : p ∈ E ∧ p.1 ≤ τ p.2
    · simp only [if_pos hp]
      calc
        |∫ z in Ioo (-1 : ℝ) 0,
          Real.exp (-(q * (p.1 : ℝ))) *
            (w (Upre p + z) - w (Upre p)) ∂X.ν| ≤
          ∫ z in Ioo (-1 : ℝ) 0,
            |Real.exp (-(q * (p.1 : ℝ))) *
              (w (Upre p + z) - w (Upre p))| ∂X.ν :=
          abs_integral_le_integral_abs
        _ ≤ C := by
          simpa only [C] using
            avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
              X hBV w K a b (Upre p) hLip (hE p hp.1) q hq p.1
        _ ≤ |C| := le_abs_self C
    · simpa only [if_neg hp, integral_zero, abs_zero] using abs_nonneg C
  have hConstant : Integrable (fun _ : ℝ≥0 × Ω => |C|)
      (clock.prod P) := integrable_const _
  have hInt : Integrable F (clock.prod P) :=
    hConstant.mono' (by simpa only [clock] using hMeas)
      (Filter.Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs, abs_abs] using hBound p))
  exact ⟨hInt, hInt.integral_prod_right⟩
