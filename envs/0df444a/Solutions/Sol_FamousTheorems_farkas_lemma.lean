-- Prove2me | solution 1 for FamousTheorems.farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:35.293393+00:00
-- url     : https://prove2.me/submissions/3bf079b3-f9bb-4f74-b165-6b156bb1733e

import Mathlib

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {C : ProperCone ℝ E}
    {f : E →L[ℝ] F} {b : F} :
    b ∈ C.map f ↔ ∀ y : F, ContinuousLinearMap.adjoint f y ∈ ProperCone.innerDual (C : Set E) →
      0 ≤ inner ℝ b y :=
  ProperCone.relative_hyperplane_separation
