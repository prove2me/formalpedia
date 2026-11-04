-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_epsilon_large_raw_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:56:55.213964+00:00
-- url     : https://prove2.me/submissions/bd71211d-195a-4251-913b-c7854eed2ce6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-ε)) X.ν := by
  have hlarge : IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iic (-1 : ℝ)) X.ν :=
    generatorIntegrand_large_negative_integrable X w y hgen
  have hmid : IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν :=
    avram_p4_c_generator_finite_band_raw_integrable X w y ε hε hgen
  have hε1' : (-1 : ℝ) < -ε := by linarith
  have hU : (Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) (-ε)) = Iio (-ε) := by
    ext z
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact lt_of_le_of_lt h hε1'
      · exact h
    · intro hz
      by_cases h : z ≤ -1
      · exact Or.inl h
      · exact Or.inr ⟨lt_of_not_ge h, hz⟩
  rw [← hU]
  exact hlarge.union hmid
