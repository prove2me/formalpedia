-- Prove2me | solution 1 for DiscreteExpectation.rsIntegral_identity_step_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:33:50.281473+00:00
-- url     : https://prove2.me/submissions/5dde2c2c-6da9-44b2-8e89-a6e7d47666c3

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
import Theorems.Thm_DiscreteExpectation_sum_bound_helper
import Theorems.Thm_taggedCommonLimit_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DiscreteExpectation
open scoped BigOperators Pointwise
noncomputable section

theorem solution {c a b : ℝ} (ha : a < c) (hb : c < b)
    (h : RSIntegrable (fun x => x) (stepIndicator c) a b) :
    rsIntegral (fun x => x) (stepIndicator c) a b h = c := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec h)
    (taggedCommonLimit_identity_step ha hb)
