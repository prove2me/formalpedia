-- Prove2me | solution 1 for Csg.cbStageValue_t5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:02:08.578849+00:00
-- url     : https://prove2.me/submissions/a3218d51-1a9d-474f-a1e5-38ec5644eeec

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_t5
import Theorems.Thm_Csg_cbStageValue_const

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) : cbCSG.stageValue .t5 v = v .t4 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t5 i j + cbCSG.expect .t5 i j v = v .t4
  rw [cbCSG_r, cbExpect_t5]; ring
end Csg
