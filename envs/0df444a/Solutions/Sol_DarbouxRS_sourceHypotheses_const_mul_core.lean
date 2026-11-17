-- Prove2me | solution 1 for DarbouxRS.sourceHypotheses_const_mul_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:51:50.19288+00:00
-- url     : https://prove2.me/submissions/c13a001b-db05-4d47-973b-9bee81dd12fc

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F001
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddAbove.smul_of_nonpos hc' hAbove
