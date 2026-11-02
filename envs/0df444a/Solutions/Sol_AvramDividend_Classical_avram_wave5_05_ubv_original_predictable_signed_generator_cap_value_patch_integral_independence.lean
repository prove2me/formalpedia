-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:26:20.276214+00:00
-- url     : https://prove2.me/submissions/f10d6edc-9350-44ce-845e-0bd07d2fb59b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The signed original generator drift integral is independent of how
an interior-only verification candidate is patched at exact cap
contact. Values at the cap can be arbitrary, including if U0=c.
The result concerns fixed atomless physical clocks, not local time.
-/

/-- Signed source generator physical-time integrals ignore cap patches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ) =
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ) := by
  have hOcc :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hD μ hCap
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hD μ
  filter_upwards [hOcc, hChron] with ω hωOcc hωChron
  intro F G hFG
  apply integral_congr_ae
  filter_upwards [hωOcc, hωChron] with t htOcc htChron
  by_cases hLive : 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
  · have hNotCap : Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c := by
      intro hAtCap
      have hEq := htChron hLive.1
      have hBookCap : riskProcess X x D t ω = c := by
        calc
          riskProcess X x D t ω =
              Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t :=
            hEq.symm
          _ = c := hAtCap
      exact (ne_of_lt (htOcc hLive)) hBookCap
    simp [hLive, hFG t hLive.1 hLive.2 hNotCap]
  · simp [hLive]
