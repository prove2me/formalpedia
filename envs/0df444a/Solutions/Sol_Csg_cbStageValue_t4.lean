-- Prove2me | solution 1 for Csg.cbStageValue_t4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:02:02.084048+00:00
-- url     : https://prove2.me/submissions/5e801472-7b72-4d3a-8674-4f461299abee

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_t4
import Theorems.Thm_Csg_cbStageValue_const

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) : cbCSG.stageValue .t4 v = v .t5 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t4 i j + cbCSG.expect .t4 i j v = v .t5
  rw [cbCSG_r, cbExpect_t4]; ring
end Csg
