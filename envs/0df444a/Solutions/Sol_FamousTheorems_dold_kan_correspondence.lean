-- Prove2me | solution 1 for FamousTheorems.dold_kan_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:11:11.928032+00:00
-- url     : https://prove2.me/submissions/10e6dc82-b576-4277-8e0f-34b932019aa9

import Mathlib

theorem solution {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Preadditive C] [CategoryTheory.IsIdempotentComplete C]
    [CategoryTheory.Limits.HasFiniteCoproducts C] :
    Nonempty (CategoryTheory.Equivalence (CategoryTheory.SimplicialObject C) (ChainComplex C ℕ)) :=
  ⟨CategoryTheory.Idempotents.DoldKan.equivalence⟩
