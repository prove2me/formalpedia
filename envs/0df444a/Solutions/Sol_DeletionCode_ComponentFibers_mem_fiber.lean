-- Prove2me | solution 1 for DeletionCode.ComponentFibers.mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:11:47.892978+00:00
-- url     : https://prove2.me/submissions/93ee154d-bbd4-4ed5-90db-b60454ddf739

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators
namespace DeletionCode.ComponentFibers
theorem _root_.solution {A C : Type*} [Fintype A] (f : A → C) (c : C) (a : A) :
    a ∈ fiber f c ↔ f a = c := by
  classical
  simp [fiber]
end DeletionCode.ComponentFibers
