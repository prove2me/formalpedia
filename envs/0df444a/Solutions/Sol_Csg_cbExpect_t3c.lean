-- Prove2me | solution 1 for Csg.cbExpect_t3c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:42.152971+00:00
-- url     : https://prove2.me/submissions/8182e4cc-da9c-43f4-9e20-911b14ab3682

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
theorem _root_.solution (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .c v = v .t3 := cbExpect_pure v .t3 .t3 a1 .c rfl
end Csg
