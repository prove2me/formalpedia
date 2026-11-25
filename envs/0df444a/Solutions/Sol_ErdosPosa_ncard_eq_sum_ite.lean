-- Prove2me | solution 1 for ErdosPosa.ncard_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:50.035114+00:00
-- url     : https://prove2.me/submissions/6c94afcc-0eff-4c88-8ed9-98cb48eaac17

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Fintype V] (p : V → Prop) [DecidablePred p] :
    {x | p x}.ncard = ∑ x, if p x then 1 else 0 := by
  rw [← Finset.card_filter, ← Set.ncard_coe_finset]
  congr 1; ext; simp
end ErdosPosa
