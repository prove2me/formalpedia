-- Prove2me | solution 1 for Csg.cbT2A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:00.599803+00:00
-- url     : https://prove2.me/submissions/f67898b7-79e9-40f7-adc7-65f30eeb8b7d

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_t2b
import Theorems.Thm_Csg_cbExpect_t2d

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t2 v).A i j = if i = .b then v .t2 else (v .t1 + v .t3) / 2 := by
  change cbCSG.r .t2 i j + cbCSG.expect .t2 i j v = if i = .b then v .t2 else (v .t1 + v .t3) / 2
  rw [cbCSG_r]
  rcases i with _ | _
  · rw [cbExpect_t2b]; simp
  · rw [cbExpect_t2d]; simp
end Csg
