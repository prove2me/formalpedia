-- Prove2me | solution 1 for Comp.CsgQ.not_answers_discounted_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:24.300801+00:00
-- url     : https://prove2.me/submissions/cd62073a-5523-45ca-88be-f593e3f6edbb

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_Reach
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_Objective

set_option autoImplicit true
open Comp
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (l : ℚ)
    (c : Finset S) : ¬ G.Answers h (Objective.discounted l) (Answer.region c) := by
  intro ha
  cases ha
end Comp.CsgQ
