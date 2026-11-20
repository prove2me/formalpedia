-- Prove2me | solution 1 for DeletionCode.ComponentFibers.fiber_card_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:51.361847+00:00
-- url     : https://prove2.me/submissions/793e6e96-a495-4588-a049-ecabdcc43bed

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators
namespace DeletionCode.ComponentFibers
theorem _root_.solution {A C : Type*} [Fintype A] (f : A → C) (c : C) :
    (fiber f c).card = 1 ↔ SingletonFiber f c := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hamem : a ∈ fiber f c := by rw [ha]; exact Finset.mem_singleton_self a
    refine ⟨a, (mem_fiber f c a).mp hamem, ?_⟩
    intro b hb
    have hbmem := (mem_fiber f c b).mpr hb
    rw [ha] at hbmem
    exact Finset.mem_singleton.mp hbmem
  · rintro ⟨a, ha, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨a, ?_⟩
    ext b
    simp only [mem_fiber, Finset.mem_singleton]
    constructor
    · exact huniq b
    · intro hb
      simpa only [hb] using ha
end DeletionCode.ComponentFibers
