-- Prove2me | solution 1 for FamousTheorems.gelfand_mazur
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:14:16.939611+00:00
-- url     : https://prove2.me/submissions/ea74e926-8e4b-46cc-b54b-cff0630a89ec

import Mathlib

theorem solution {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    Nonempty (ℂ ≃ₐ[ℂ] A) :=
  ⟨NormedRing.algEquivComplexOfComplete hA⟩
