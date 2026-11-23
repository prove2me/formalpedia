-- Prove2me | solution 1 for Csg.cbGClosed_cbVStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:01:28.405717+00:00
-- url     : https://prove2.me/submissions/8ea85b52-4e26-4388-9dca-0189eb60d6e4

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : cbGClosed cbVStar = cbVStar := by
  funext s
  apply Subtype.ext
  change cbGClosedVal (fun s' => (cbVStar s' : ℝ)) s = cbVStarVal s
  cases s <;> unfold cbGClosedVal cbVStarVal cbVStar cbVStarVal <;> norm_num
end Csg
