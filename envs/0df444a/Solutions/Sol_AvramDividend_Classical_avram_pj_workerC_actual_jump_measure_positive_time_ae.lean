-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_jump_measure_positive_time_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:43:22.215096+00:00
-- url     : https://prove2.me/submissions/229e0940-40b8-48b7-83fa-8dbfa05d9adf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ᵐ p ∂((Measure.count.restrict {s : ℝ≥0 |
       0 < s ∧ X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))),
      p.1 ≠ 0 := by
  have hz :
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) = 0 :=
    avram_wave5_01_actual_source_jump_measure_zero_initial_time
      X ω Set.univ MeasurableSet.univ
  have heq : ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) =
      {p : ℝ≥0 × ℝ | p.1 = 0} := by ext p; simp
  rw [heq] at hz
  exact ae_iff.mpr (by simpa using hz)

