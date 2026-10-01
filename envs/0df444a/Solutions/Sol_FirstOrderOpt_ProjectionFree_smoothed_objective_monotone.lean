-- Prove2me | solution 1 for FirstOrderOpt.ProjectionFree.smoothed_objective_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T14:04:00.386844+00:00
-- url     : https://prove2.me/submissions/658b54e6-d420-4e06-a792-f8aaa35954b5

import Mathlib

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (Y : Set F) (A : E →L[ℝ] F) (fhat V : F → ℝ) (DY : ℝ)
    (hVbound : ∀ y ∈ Y, V y ≤ DY ^ 2)
    (fη : ℝ → E → ℝ)
    (hfη : ∀ η x, fη η x = sSup ((fun y => ⟪A x, y⟫ - fhat y - η * (V y - DY ^ 2)) '' Y))
    (η1 η2 : ℝ) (hη : η2 ≤ η1) (hη2 : 0 ≤ η2) (x : E)
    (hbdd : ∀ η, 0 ≤ η → BddAbove ((fun y => ⟪A x, y⟫ - fhat y - η * (V y - DY ^ 2)) '' Y)) :
    fη η2 x ≤ fη η1 x := by
  rw [hfη, hfη]
  rcases Y.eq_empty_or_nonempty with hY | hY
  · subst hY
    simp
  · apply csSup_le (hY.image _)
    rintro _ ⟨y, hy, rfl⟩
    have h1 : ⟪A x, y⟫ - fhat y - η2 * (V y - DY ^ 2)
        ≤ ⟪A x, y⟫ - fhat y - η1 * (V y - DY ^ 2) := by
      have := hVbound y hy
      nlinarith
    exact h1.trans (le_csSup (hbdd η1 (hη2.trans hη)) ⟨y, hy, rfl⟩)

