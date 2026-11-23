-- Prove2me | solution 1 for Csg.cbT3A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:02:54.920685+00:00
-- url     : https://prove2.me/submissions/81611c4d-2167-4fa6-bc2a-5ee209d3bef2

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_t3c
import Theorems.Thm_Csg_cbExpect_t3d

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t3 v).A i j = if j = .c then v .t3 else (v .t2 + v .t4) / 2 := by
  change cbCSG.r .t3 i j + cbCSG.expect .t3 i j v = if j = .c then v .t3 else (v .t2 + v .t4) / 2
  rw [cbCSG_r]
  rcases j with _ | _
  · rw [cbExpect_t3c]; simp
  · rw [cbExpect_t3d]; simp
end Csg
