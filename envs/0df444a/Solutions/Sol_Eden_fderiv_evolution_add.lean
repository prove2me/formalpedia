-- Prove2me | solution 1 for Eden.fderiv_evolution_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:23.037153+00:00
-- url     : https://prove2.me/submissions/702537b9-bb74-4fc7-b12c-5b6d41e257c8

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
import Theorems.Thm_Eden_contDiff_evolution
import Theorems.Thm_Eden_evolution_add


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) := by
  have he : evolution c (s + t) = (evolution c t) ∘ (evolution c s) :=
    funext (evolution_add c hs ht)
  rw [he]
  exact fderiv_comp p ((contDiff_evolution c ht 1).differentiable one_ne_zero _)
    ((contDiff_evolution c hs 1).differentiable one_ne_zero p)
end Eden
