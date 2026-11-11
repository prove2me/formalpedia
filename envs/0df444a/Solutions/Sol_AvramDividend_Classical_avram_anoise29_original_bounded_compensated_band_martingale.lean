-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise29_original_bounded_compensated_band_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:25:09.158224+00:00
-- url     : https://prove2.me/submissions/1936345b-5bc2-47dc-82cc-a86cb2698773

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise30_original_smallband_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_avram_anoise31_original_smallband_signed_rightcont_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Separate original finite-count integrability from original right-continuous filtration centring. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ,
      (∀ t : ℝ≥0, Integrable
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P) ∧
      (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω =
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) := by
  have hI := avram_anoise30_original_smallband_compensator_integrable X hFinite
  intro n
  exact ⟨hI n,
    avram_anoise31_original_smallband_signed_rightcont_condexp X hFinite hI n⟩
