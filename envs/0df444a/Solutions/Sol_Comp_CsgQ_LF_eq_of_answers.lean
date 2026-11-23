-- Prove2me | solution 1 for Comp.CsgQ.LF_eq_of_answers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:03:32.931802+00:00
-- url     : https://prove2.me/submissions/82955253-b33b-4fee-bafe-bc0f68627d4d

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
    (ha : G.Answers h (Objective.limitReach target) (Answer.region c)) :
    (G.toCSG h).LF ↑target = (↑c : Set S) := by
  cases ha with
  | limitReach hLF => exact hLF
end Comp.CsgQ
