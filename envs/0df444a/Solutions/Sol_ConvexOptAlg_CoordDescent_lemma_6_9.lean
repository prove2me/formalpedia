-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.lemma_6_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:03:41.584007+00:00
-- url     : https://prove2.me/submissions/099ec35d-9242-4dd0-883c-e485896828a4

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

open ConvexOptAlg.CoordDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (f' : E → (E →L[ℝ] ℝ)) (α : ℝ) (hα : 0 < α)
    (hsc : IsStronglyConvexNorm f f' α)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) :
    f x - f xstar ≤ 1 / (2 * α) * ‖f' x‖ ^ 2 := by
  have h1 := hsc.2 x xstar
  have h2 : f' x (x - xstar) ≤ ‖f' x‖ * ‖x - xstar‖ :=
    le_trans (le_abs_self _) ((f' x).le_opNorm (x - xstar))
  set G := ‖f' x‖
  set t := ‖x - xstar‖
  have key : G * t - α / 2 * t ^ 2 ≤ 1 / (2 * α) * G ^ 2 := by
    have e : 1 / (2 * α) * G ^ 2 - (G * t - α / 2 * t ^ 2) = (α * t - G) ^ 2 / (2 * α) := by
      field_simp; ring
    have : 0 ≤ (α * t - G) ^ 2 / (2 * α) := by positivity
    linarith
  linarith
