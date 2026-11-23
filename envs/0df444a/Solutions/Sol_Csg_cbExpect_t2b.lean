-- Prove2me | solution 1 for Csg.cbExpect_t2b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:24.450877+00:00
-- url     : https://prove2.me/submissions/d2f0d531-0522-4442-bb35-f20aad7fb4b8

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
theorem _root_.solution (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .b a2 v = v .t2 := cbExpect_pure v .t2 .t2 .b a2 rfl
end Csg
