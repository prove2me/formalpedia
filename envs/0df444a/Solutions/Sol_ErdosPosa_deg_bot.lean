-- Prove2me | solution 1 for ErdosPosa.deg_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:05.655461+00:00
-- url     : https://prove2.me/submissions/d97d0713-95c5-4b5b-b639-496b00565a22

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution (v : V) : deg (⊥ : SimpleGraph V) v = 0 := by
  rw [deg, show (⊥ : SimpleGraph V).neighborSet v = ∅ from by ext; simp, Set.ncard_empty]
end ErdosPosa
