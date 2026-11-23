-- Prove2me | solution 1 for Csg.cbExpect_t5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:28.524768+00:00
-- url     : https://prove2.me/submissions/445bdea8-a77b-41f1-acbe-d2d3a06dfd92

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
    cbCSG.expect .t5 a1 a2 v = v .t4 := cbExpect_pure v .t5 .t4 a1 a2 rfl
end Csg
