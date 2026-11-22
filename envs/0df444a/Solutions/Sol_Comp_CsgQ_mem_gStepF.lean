-- Prove2me | solution 1 for Comp.CsgQ.mem_gStepF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:56:26.771089+00:00
-- url     : https://prove2.me/submissions/214fc311-6bd6-476a-a516-d105446046e3

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_CsgQ_mem_pre1F
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.CsgQ.mem_pre1F

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (safe x : Finset S) (s : S) :
    s ∈ G.gStepF safe x ↔ s ∈ G.pre1F x ∧ s ∈ safe := by
  simp [gStepF]
end Comp.CsgQ
