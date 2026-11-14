-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:18:14.759207+00:00
-- url     : https://prove2.me/submissions/21101485-31e7-4379-857e-4432e4950803

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

/-- Convert an original stopped Gaussian extended nonnegative expected energy
limit to a real expected L1 limit once each real energy is integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (T m) P)
    (hNonneg : ∀ m, ∀ᵐ ω ∂P, 0 ≤ T m ω)
    (hL : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (T m ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun m => ∫ ω, T m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hEq (m : ℕ) :
      (∫ ω, T m ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal (T m ω) ∂P).toReal := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hI m) (hNonneg m)]
    rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae (hNonneg m))]
  have hReal : Tendsto
      (fun m => (∫⁻ ω, ENNReal.ofReal (T m ω) ∂P).toReal)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal
        (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hL
  exact hReal.congr' (Filter.Eventually.of_forall
    (fun m => (hEq m).symm))
