-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_jump_measure_negative_mark_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:26:53.704417+00:00
-- url     : https://prove2.me/submissions/dfd988fa-75be-4509-88ef-e9f1b68c9a81

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
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
    ∀ᵐ p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))),
      p.2 < 0 := by
  exact avram_pj_workerC_original_NX_ae_negative_jumps X ω
