-- Prove2me | solution 1 for Comp.CsgQ.coe_gStepF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:30:58.427437+00:00
-- url     : https://prove2.me/submissions/bc1d4dbe-ea9d-47de-86a8-071cc8bc524f

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_coe_pre1F
attribute [local simp] Comp.CsgQ.coe_supportF

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (safe x : Finset S) :
    (↑(G.gStepF safe x) : Set S) = G.GStepQ ↑safe ↑x := by
  simp only [gStepF, GStepQ, Finset.coe_inter, coe_pre1F]
end Comp.CsgQ
