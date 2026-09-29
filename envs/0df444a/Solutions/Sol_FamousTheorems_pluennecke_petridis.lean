-- Prove2me | solution 1 for FamousTheorems.pluennecke_petridis
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:56:16.232994+00:00
-- url     : https://prove2.me/submissions/20e014fb-c606-4626-8eaf-6799780a90bb

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} (C : Finset G)
    (hA : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card) :
    (C + A + B).card * A.card ≤ (A + B).card * (C + A).card := by
  exact Finset.pluennecke_petridis_inequality_add C hA
