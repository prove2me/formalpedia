-- Prove2me | solution 1 for BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T21:44:20.416933+00:00
-- url     : https://prove2.me/submissions/d315f7d6-1bfb-4fc0-8b1e-43da93460381

import Mathlib
import Definitions.Def_ChapterBayesInference

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterBayesInference in open BookProof.ChapterBayesInference in open scoped BigOperators in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {prior : X → ℝ} {L : X → Y → ℝ} (y : Y) (x : X) :
    posterior prior L y x = joint prior L x y / evidence prior L y := by
  intros
  rfl
