-- Prove2me | solution 1 for Comp.CsgQ.AF_eq_of_answers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:03:17.794194+00:00
-- url     : https://prove2.me/submissions/b019fdf3-3fff-439c-8e44-3d9d1eae4d3e

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
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) {target c : Finset S}
    (ha : G.Answers h (Objective.almostReach target) (Answer.region c)) :
    (G.toCSG h).AF ↑target = (↑c : Set S) := by
  cases ha with
  | almostReach hAF => exact hAF
end Comp.CsgQ
