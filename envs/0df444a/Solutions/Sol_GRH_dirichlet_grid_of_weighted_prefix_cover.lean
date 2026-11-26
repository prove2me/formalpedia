-- Prove2me | solution 1 for GRH.dirichlet_grid_of_weighted_prefix_cover
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:18:20.084621+00:00
-- url     : https://prove2.me/submissions/33be78da-9543-461f-9c9d-a616ba35a883

import Theorems.Thm_GRH_dirichlet_nonzero_of_weighted_prefix_cover
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid

open GRH.DirichletGrid GRH.DirichletPrefix

/-- The arithmetic weighted-prefix test supplies the specified finite
Dirichlet-polynomial grid on the full closed rectangle. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hH : 0 ≤ H) (hw : Covers d a b H) : ∃ m : ℕ, Passes χ a b H m := by
  apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid d χ hχ a b H ha hab hb hH).1
  intro z hz
  exact GRH.dirichlet_nonzero_of_weighted_prefix_cover d χ hχ a b H hw z hz.1.1 hz.1.2 (abs_le.mpr hz.2)
