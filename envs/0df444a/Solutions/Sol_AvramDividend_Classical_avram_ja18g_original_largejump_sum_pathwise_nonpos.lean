-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_largejump_sum_pathwise_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:48:22.228197+00:00
-- url     : https://prove2.me/submissions/9b397c62-71d2-4d8f-b70c-f1d86776f869

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original physical jump mark in the large-negative band is nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (t : ℝ≥0) (ω : Ω),
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ≤ 0 := by
  intro t ω
  unfold avram_p4_h_gaussian_intrinsic_large_jump_sum
  have hm : MeasurableSet (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)) :=
    measurableSet_Ioc.prod measurableSet_Iic
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem hm] with p hp
  exact le_trans hp.2 (by norm_num)
