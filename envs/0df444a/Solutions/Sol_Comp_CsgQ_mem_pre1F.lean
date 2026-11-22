-- Prove2me | solution 1 for Comp.CsgQ.mem_pre1F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:56.331264+00:00
-- url     : https://prove2.me/submissions/86d4202a-42e9-4c03-82a2-959cab3b8462

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_supportF
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_supportF

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (x : Finset S) (s : S) :
    s ∈ G.pre1F x ↔ ∃ a1, ∀ a2, G.supportF s a1 a2 ⊆ x := by
  simp [pre1F]
end Comp.CsgQ
