-- Prove2me | solution 1 for DeletionCode.ComponentFibers.component_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:03.829609+00:00
-- url     : https://prove2.me/submissions/96408c59-d94f-40ec-b129-a5e215b4b3f2

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers
import Theorems.Thm_DeletionCode_ComponentFibers_singleton_fiber_count_bound

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators
namespace DeletionCode.ComponentFibers
theorem _root_.solution {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (hsurj : Function.Surjective f) (t R : ℕ)
    (hA : Fintype.card A = 2 * t * R)
    (hsingle : Fintype.card {c : C // SingletonFiber f c} ≤ 2 * t) :
    Fintype.card C ≤ t * R + t := by
  have h := singleton_fiber_count_bound f hsurj
  rw [hA, Nat.mul_assoc] at h
  omega
end DeletionCode.ComponentFibers
