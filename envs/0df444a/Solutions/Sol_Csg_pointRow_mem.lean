-- Prove2me | solution 1 for Csg.pointRow_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:02:21.79547+00:00
-- url     : https://prove2.me/submissions/8a96dd74-8930-4f35-adcc-1107def2a5d0

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_rowMove_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (m : RowMove) : pointRow m ∈ stdSimplex ℝ RowMove := by
  refine ⟨fun i => by unfold pointRow; split_ifs <;> norm_num, ?_⟩
  unfold pointRow; rw [rowMove_sum]; cases m <;> simp
end Csg
