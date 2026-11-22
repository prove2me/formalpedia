-- Prove2me | solution 1 for Csg.pointCol_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:02:58.587658+00:00
-- url     : https://prove2.me/submissions/5a8c430f-dab4-4ac0-961c-c22e95724677

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_colMove_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (m : ColMove) : pointCol m ∈ stdSimplex ℝ ColMove := by
  refine ⟨fun j => by unfold pointCol; split_ifs <;> norm_num, ?_⟩
  unfold pointCol; rw [colMove_sum]; cases m <;> simp
end Csg
