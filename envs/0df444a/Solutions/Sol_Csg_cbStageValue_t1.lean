-- Prove2me | solution 1 for Csg.cbStageValue_t1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:01:10.333346+00:00
-- url     : https://prove2.me/submissions/7edc13e6-7e14-434f-bbc7-3959a66c6905

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_t1
import Theorems.Thm_Csg_cbStageValue_const

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) : cbCSG.stageValue .t1 v = v .t1 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t1 i j + cbCSG.expect .t1 i j v = v .t1
  rw [cbCSG_r, cbExpect_t1]; ring
end Csg
