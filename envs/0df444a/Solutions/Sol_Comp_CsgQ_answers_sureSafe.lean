-- Prove2me | solution 1 for Comp.CsgQ.answers_sureSafe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:07:57.039801+00:00
-- url     : https://prove2.me/submissions/cdbc9146-bf96-4762-ad38-a8f974e9a150

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_Reach
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_Objective
import Theorems.Thm_Comp_CsgQ_G_eq_coe_of_fixed


set_option autoImplicit true
open Comp
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (region c : Finset S) (n : ℕ)
    (hiter : (G.gStepF region)^[n] Finset.univ = c) (hfix : G.gStepF region c = c) :
    G.Answers h (Objective.sureSafe region) (Answer.region c) :=
  .sureSafe (G_eq_coe_of_fixed G h region c n hiter hfix)
end Comp.CsgQ
