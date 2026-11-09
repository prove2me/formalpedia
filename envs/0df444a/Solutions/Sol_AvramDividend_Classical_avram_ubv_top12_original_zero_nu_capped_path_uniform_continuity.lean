-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:34:14.355632+00:00
-- url     : https://prove2.me/submissions/c02d5b0a-82ae-4fc2-8564-6451e38ee992

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, UniformContinuousOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 T) := by
  have hcontinuous : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω) :=
    avram_ubv_top11_original_zero_nu_global_continuous_ae X hν
  filter_upwards [hcontinuous] with ω hω
  exact isCompact_Icc.uniformContinuousOn_of_continuous hω.continuousOn
