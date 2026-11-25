-- Prove2me | solution 1 for ErdosPosa.ncard_support_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:56.47425+00:00
-- url     : https://prove2.me/submissions/869ad942-a808-4a25-8e67-c128eebeb5cd

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution {u v : V} (p : H.Walk u v) : {y | y ∈ p.support}.ncard ≤ p.length + 1 := by
  classical
  have : {y | y ∈ p.support} = ↑p.support.toFinset := by ext; simp
  rw [this, Set.ncard_coe_finset, ← Walk.length_support]
  exact List.toFinset_card_le _
end ErdosPosa
