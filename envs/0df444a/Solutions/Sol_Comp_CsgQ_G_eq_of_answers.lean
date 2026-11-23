-- Prove2me | solution 1 for Comp.CsgQ.G_eq_of_answers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:58.503806+00:00
-- url     : https://prove2.me/submissions/8e4abc6b-4f8f-48ea-9fa5-a9f74c164644

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
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) {region c : Finset S}
    (ha : G.Answers h (Objective.sureSafe region) (Answer.region c)) :
    (G.toCSG h).G ↑region = (↑c : Set S) := by
  cases ha with
  | sureSafe hG => exact hG
end Comp.CsgQ
