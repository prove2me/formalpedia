-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:52:33.575246+00:00
-- url     : https://prove2.me/submissions/e0952926-a36b-472d-8833-4438a340a5d7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_band_compensation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν := by
  have hεneg : -ε < (0 : ℝ) := by linarith
  have hK : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν := hgen.mono_set (by
    intro z hz
    exact lt_trans hz.2 hεneg)
  have hz : IntegrableOn (fun z : ℝ => z)
      (Ioo (-1 : ℝ) (-ε)) X.ν :=
    avram_p4_c_generator_cutoff_linear_mark_integrable X ε hε
  have hlin : IntegrableOn (fun z : ℝ => deriv w y * z)
      (Ioo (-1 : ℝ) (-ε)) X.ν := hz.const_mul (deriv w y)
  have hsum : IntegrableOn
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand w y z + deriv w y * z)
      (Ioo (-1 : ℝ) (-ε)) X.ν := hK.add hlin
  have hsame : Set.EqOn
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand w y z + deriv w y * z)
      (fun z : ℝ => w (y + z) - w y)
      (Ioo (-1 : ℝ) (-ε)) := by
    intro z hzS
    change SpectrallyNegativeLevy.generatorIntegrand w y z + deriv w y * z =
      w (y + z) - w y
    rw [avram_p4_c_generator_cutoff_band_compensation_identity w y z ε hε hzS]
    ring
  exact hsum.congr_fun hsame measurableSet_Ioo
