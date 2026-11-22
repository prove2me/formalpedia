-- Prove2me | solution 1 for Comp.CsgQ.mem_supportF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:35.587212+00:00
-- url     : https://prove2.me/submissions/ec46f60b-bcc6-4124-9b8a-4be25bcbf4c4

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_supportF
attribute [local simp] Comp.CsgQ.coe_supportF

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    s' ∈ G.supportF s a1 a2 ↔ G.K s a1 a2 s' ≠ 0 := by
  simp [supportF]
end Comp.CsgQ
