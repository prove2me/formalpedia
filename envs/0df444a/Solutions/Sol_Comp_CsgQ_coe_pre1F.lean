-- Prove2me | solution 1 for Comp.CsgQ.coe_pre1F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:13.055736+00:00
-- url     : https://prove2.me/submissions/548f8c14-d641-4647-84a0-38ea68af5f4e

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
theorem _root_.solution (G : CsgQ S A1 A2) (x : Finset S) :
    (↑(G.pre1F x) : Set S) = G.Pre1Q ↑x := by
  have key : ∀ (s : S) (a1 : A1) (a2 : A2),
      (G.supportF s a1 a2 ⊆ x) ↔ (G.supportQ s a1 a2 ⊆ (↑x : Set S)) := by
    intro s a1 a2
    rw [← coe_supportF G s a1 a2, Finset.coe_subset]
  ext s
  simp only [Finset.mem_coe, pre1F, Finset.mem_filter, Finset.mem_univ, true_and, Pre1Q,
    Set.mem_setOf_eq]
  exact exists_congr fun a1 => forall_congr' fun a2 => key s a1 a2
end Comp.CsgQ
