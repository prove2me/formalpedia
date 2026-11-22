-- Prove2me | solution 1 for Comp.CsgQ.toCSG_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:06:17.319514+00:00
-- url     : https://prove2.me/submissions/b868fd12-10c3-4fc2-b679-cb9b4dcc8c21

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_toPMF_support
attribute [local simp] Comp.CsgQ.coe_supportF



set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).K s a1 a2).support = (↑(G.supportF s a1 a2) : Set S) := by
  rw [coe_supportF]
  exact toPMF_support G h s a1 a2
end Comp.CsgQ
