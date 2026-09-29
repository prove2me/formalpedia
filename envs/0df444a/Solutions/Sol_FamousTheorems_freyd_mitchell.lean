-- Prove2me | solution 1 for FamousTheorems.freyd_mitchell
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:18:12.686303+00:00
-- url     : https://prove2.me/submissions/c67c74e1-5347-4cae-b4cd-9dfadd09a98c

import Mathlib

universe u v

theorem solution (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : CategoryTheory.Functor C (ModuleCat.{max u v} R)),
      F.Full ∧ F.Faithful ∧ CategoryTheory.Limits.PreservesFiniteLimits F ∧
        CategoryTheory.Limits.PreservesFiniteColimits F :=
  CategoryTheory.Abelian.freyd_mitchell C
