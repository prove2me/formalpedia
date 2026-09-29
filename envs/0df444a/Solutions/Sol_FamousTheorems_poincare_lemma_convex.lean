-- Prove2me | solution 1 for FamousTheorems.poincare_lemma_convex
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:55:03.122366+00:00
-- url     : https://prove2.me/submissions/bd0d7a8e-f924-4c5e-82fe-b3e2e33c392f

import Mathlib

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {ω : E → E →L[𝕜] F}
    (hs : Convex ℝ s) (hso : IsOpen s) (hω : DifferentiableOn ℝ ω s)
    (hsymm : ∀ a ∈ s, ∀ x y : E, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f : E → F, ∀ a ∈ s, HasFDerivAt f (ω a) a :=
  hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso hω hsymm
