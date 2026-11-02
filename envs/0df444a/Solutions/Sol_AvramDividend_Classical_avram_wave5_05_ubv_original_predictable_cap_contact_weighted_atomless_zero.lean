-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:34:18.796756+00:00
-- url     : https://prove2.me/submissions/2a29be1f-b6be-4125-9768-5631399764c6

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
Cap generator characteristics are evaluated at the predictable left-limit
controlled reserve. The original atomless-clock chronology identity transfers
actual UBV current-reserve cap occupation to this correct stochastic argument.
-/

/-- Weighted positive-time predictable cap contact contributes no clock mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t ω else 0 ∂μ) = 0 := by
  have hOcc :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hD μ hCap
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hD μ
  filter_upwards [hOcc, hChron] with ω hωOcc hωChron
  have hZero : ∀ᵐ (t : ℝ≥0) ∂μ,
      (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
       then weight t ω else 0) = 0 := by
    filter_upwards [hωOcc, hωChron] with t htOcc htChron
    by_cases hContact :
        0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
    · have hLess := htOcc ⟨hContact.1, hContact.2.1⟩
      have hEq := htChron hContact.1
      have hAtCap : riskProcess X x D t ω = c := by
        calc
          riskProcess X x D t ω =
              Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t :=
              hEq.symm
          _ = c := hContact.2.2
      rw [hAtCap] at hLess
      exact False.elim ((lt_irrefl c) hLess)
    · simp [hContact]
  calc
    (∫⁻ t : ℝ≥0,
      if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
      then weight t ω else 0 ∂μ) =
        ∫⁻ _t : ℝ≥0, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae hZero
    _ = 0 := by simp
