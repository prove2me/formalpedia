-- Prove2me | solution 1 for FamousTheorems.day_reflection_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:54:52.09159+00:00
-- url     : https://prove2.me/submissions/7f7a3b98-4585-4dd5-9ad3-1c680d6f2fbe

import Mathlib

open CategoryTheory MonoidalCategory

theorem solution {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalClosed D] {R : Functor C D} [R.Faithful] [R.Full] {L : Functor D C} (adj : L ⊣ R) :
    List.TFAE [∀ (c : C) (d : D), IsIso (adj.unit.app ((ihom d).obj (R.obj c))),
      ∀ (c : C) (d : D), IsIso ((MonoidalClosed.pre (adj.unit.app d)).app (R.obj c)),
      ∀ d d' : D, IsIso (L.map (adj.unit.app d ▷ d')),
      ∀ d d' : D, IsIso (L.map (adj.unit.app d ⊗ₘ adj.unit.app d'))] :=
  CategoryTheory.Monoidal.Reflective.isIso_tfae adj
