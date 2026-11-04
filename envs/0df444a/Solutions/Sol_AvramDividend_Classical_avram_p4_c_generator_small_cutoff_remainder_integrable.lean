-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_small_cutoff_remainder_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:14.434962+00:00
-- url     : https://prove2.me/submissions/d71cd062-8285-4ef9-b709-5600bc57d394

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_small_cutoff_compensation_identity

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
    IntegrableOn (fun z : ℝ => w (y + z) - w y - deriv w y * z)
      (Ico (-ε) (0 : ℝ)) X.ν := by
  have hK : IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Ico (-ε) (0 : ℝ)) X.ν :=
    hgen.mono_set (by
      intro z hz
      exact hz.2)
  have hEq : Set.EqOn
      (SpectrallyNegativeLevy.generatorIntegrand w y)
      (fun z : ℝ => w (y + z) - w y - deriv w y * z)
      (Ico (-ε) (0 : ℝ)) := by
    intro z hz
    exact avram_p4_c_generator_small_cutoff_compensation_identity
      w y z ε hε hε1 hz
  exact hK.congr_fun hEq measurableSet_Ico
