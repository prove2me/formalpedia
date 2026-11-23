-- Prove2me | solution 1 for Csg.cbExpect_t4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:22.850169+00:00
-- url     : https://prove2.me/submissions/2763608f-22ad-4db3-89b2-f0835e8189ec

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbExpect_pure

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t4 a1 a2 v = v .t5 := cbExpect_pure v .t4 .t5 a1 a2 rfl
end Csg
