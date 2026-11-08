-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:41:11.746411+00:00
-- url     : https://prove2.me/submissions/20db9604-db25-45b1-81b2-148f7b89bdb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact positive closed-cap BV generator harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ∀ y : ℝ, 0 < y → y ≤ (cstar W).toReal →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y = 0 := by
  intro y hy hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact generator_vcstar_eq_zero_bv_unconditional_20261026
      X hX hBV q hq W hW hcpos y ⟨hy, hlt⟩
  · rw [heq]
    exact avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
      X hX q hq W hW hc hcpos (Or.inr (Or.inl hBV))
