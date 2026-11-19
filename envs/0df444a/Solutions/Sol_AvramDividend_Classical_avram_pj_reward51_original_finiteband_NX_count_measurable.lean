-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward51_original_finiteband_NX_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:17:22.265896+00:00
-- url     : https://prove2.me/submissions/a8969b36-1abe-49be-b1e4-43cb3040e365

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (η : ℝ) :
    Measurable (fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (0 : ℝ≥0) T ×ˢ Ioo (-1 : ℝ) (-η))) := by
  obtain ⟨κ, hκ, hκeq⟩ := avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hset : MeasurableSet (Ioc (0 : ℝ≥0) T ×ˢ Ioo (-1 : ℝ) (-η)) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hm : Measurable (fun ω => (κ ω)
      (Ioc (0 : ℝ≥0) T ×ˢ Ioo (-1 : ℝ) (-η))) :=
    κ.measurable_coe hset
  simpa only [hκeq] using hm
