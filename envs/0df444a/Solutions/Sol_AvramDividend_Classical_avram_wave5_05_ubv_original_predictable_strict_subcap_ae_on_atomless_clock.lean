-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:43:37.401245+00:00
-- url     : https://prove2.me/submissions/351c399a-d959-402e-874f-ecf2ae637bf8

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
On the actual original controlled UBV source, the correct
predictable chronological pre-event reserve is strictly below
the controlled finite cap at almost every positive surviving
time of any FIXED s-finite atomless physical-time clock.
Initial capital and later reserve values may equal the cap.
-/

/-- Exact original predictable reserve is strictly subcap μ-a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c := by
  have hOcc :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hD μ hCap
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hD μ
  filter_upwards [hOcc, hChron] with ω hωOcc hωChron
  filter_upwards [hωOcc, hωChron] with t htOcc htChron
  intro htPos htLive
  calc
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        riskProcess X x D t ω := htChron htPos
    _ < c := htOcc ⟨htPos, htLive⟩
