-- Prove2me | solution 1 for DeletionCode.ComponentFibers.sum_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:51.8686+00:00
-- url     : https://prove2.me/submissions/5b3794ed-d48e-4b81-880f-3f32183aad48

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
theorem _root_.solution {A C : Type*} [Fintype A] [Fintype C] (f : A → C) :
    (∑ c : C, (fiber f c).card) = Fintype.card A := by
  classical
  simpa only [fiber, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
      (Finset.univ : Finset C) f
end DeletionCode.ComponentFibers
