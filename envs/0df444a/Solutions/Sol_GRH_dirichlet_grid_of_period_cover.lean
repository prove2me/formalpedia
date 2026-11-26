-- Prove2me | solution 1 for GRH.dirichlet_grid_of_period_cover
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:42:31.400518+00:00
-- url     : https://prove2.me/submissions/a345a628-eeb1-4660-b02f-ae31867ef00d

import Theorems.Thm_GRH_dirichlet_nonzero_of_sieved_period_cover
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.Tactic.Linarith

open GRH.DirichletGrid GRH.DirichletPeriod

theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 0 ≤ H)
    (hw : Covers d a H) : ∃ m : ℕ, Passes χ a b H m := by
  apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid d χ hχ a b H ha hab hb hH).1
  exact fun z hz => GRH.dirichlet_nonzero_of_sieved_period_cover d χ hχ a H (by linarith)
    hH hw z hz.1.1 (abs_le.mpr hz.2)
