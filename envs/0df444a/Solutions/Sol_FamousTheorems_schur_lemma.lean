-- Prove2me | solution 1 for FamousTheorems.schur_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:12:09.005273+00:00
-- url     : https://prove2.me/submissions/4ad8dd5a-f365-401c-858d-846e143012fc

import Mathlib

universe u v

theorem solution {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C] (𝕜 : Type*) [Field 𝕜]
    [IsAlgClosed 𝕜] [CategoryTheory.Linear 𝕜 C] [CategoryTheory.Limits.HasKernels C] (X : C)
    [CategoryTheory.Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] : Module.finrank 𝕜 (X ⟶ X) = 1 :=
  CategoryTheory.finrank_endomorphism_simple_eq_one 𝕜 X
