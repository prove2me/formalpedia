-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_compensated_marked_source_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:09:09.094828+00:00
-- url     : https://prove2.me/submissions/235c4911-efbb-4b2a-adef-41e1726aa840

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Both original marked-jump source integrals vanish when the Lévy jump intensity
    and the intrinsic positive-time marked counting measure vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
    (Λ : Measure ℝ≥0) (g : Ω → ℝ≥0 × ℝ → ℝ) :
    ∀ᵐ ω ∂P,
      (∫ p, g ω p ∂(NX ω)) -
      (∫ t, ∫ z, g ω (t, z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂Λ) = 0 := by
  filter_upwards [
    avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae X hNuZero NX hNX
  ] with ω hω
  simp [hω, hNuZero]
