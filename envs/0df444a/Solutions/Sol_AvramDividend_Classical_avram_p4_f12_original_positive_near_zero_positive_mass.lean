-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_positive_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:10:37.62186+00:00
-- url     : https://prove2.me/submissions/3d2174c8-a378-4b73-b0ad-171089d715a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f16_sigma_nonzero_upward_germ_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_f16_sigma_zero_infinite_jump_upward_germ_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Split unbounded-variation upward regularity into Gaussian and pure-jump cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
  by_cases hσ : X.σ = 0
  · have hν : ¬ (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν < ⊤) := by
      intro hfinite
      exact hBV ⟨hσ, hfinite⟩
    exact avram_p4_f16_sigma_zero_infinite_jump_upward_germ_mass X hσ hν
  · exact avram_p4_f16_sigma_nonzero_upward_germ_mass X hσ
