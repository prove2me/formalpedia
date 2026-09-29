-- Prove2me | solution 1 for BSS.feas4_npComplete_over_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T22:07:47.214985+00:00
-- url     : https://prove2.me/submissions/e239aeb3-a5e1-4f05-aecf-b3a5103f438f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BSS_feas4_inNP
import Theorems.Thm_BSS_feas4_np_hard

open BSS in
/-- `NPCompleteOverReal Feas4 Feas4Yes` is, by definition, membership in `NP`
together with `NP`-hardness; each conjunct is one of the mission's milestones. -/
theorem solution : NPCompleteOverReal Feas4 Feas4Yes :=
  ⟨BSS.feas4_inNP, BSS.feas4_np_hard⟩
