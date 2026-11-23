-- Prove2me | solution 1 for Csg.cbExpect_t1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:20.489663+00:00
-- url     : https://prove2.me/submissions/74820d48-e89d-4481-8ede-e421ab70f039

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
    cbCSG.expect .t1 a1 a2 v = v .t1 := cbExpect_pure v .t1 .t1 a1 a2 rfl
end Csg
