-- Prove2me | solution 1 for GRH.dirichlet_band_nonzero_iff_cofinal_finite_grids
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:08:14.501709+00:00
-- url     : https://prove2.me/submissions/d4770dca-3cb0-41af-8f58-98d53eef1a0c

import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Complex GRH.DirichletGrid

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (b : ℝ) (hb : (1/2:ℝ) < b) (hb1 : b ≤ 1) :
    (∀ z : ℂ, (1/2:ℝ) < z.re → z.re ≤ b → χ.LFunction z ≠ 0) ↔
      ∀ h : ℕ, ∃ m : ℕ, Passes χ (1/2 + (b-1/2)/((h:ℝ)+1)) b ((h:ℝ)+1) m := by
  have pos (h : ℕ) : 0 < (h:ℝ)+1 := by positivity
  have left (h : ℕ) : (1/2:ℝ) < 1/2 + (b-1/2)/((h:ℝ)+1) :=
    lt_add_of_pos_right _ (div_pos (sub_pos.mpr hb) (pos h))
  have right (h : ℕ) : 1/2 + (b-1/2)/((h:ℝ)+1) ≤ b := by
    have hh := div_le_self (sub_nonneg.mpr hb.le) (show 1 ≤ (h:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) h])
    linarith
  constructor
  · intro hz h
    apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid q χ hχ _ _ _ (left h).le
      (right h) hb1 (pos h).le).1
    exact fun z hmem => hz z ((left h).trans_le hmem.1.1) hmem.1.2
  · intro grids z hzl hzr
    obtain ⟨h,hh⟩ := exists_nat_gt (max |z.im| ((b-1/2)/(z.re-1/2)))
    have hIm : |z.im| ≤ (h:ℝ)+1 := by linarith [(le_max_left ..).trans_lt hh]
    have hdiv := (div_lt_iff₀ (sub_pos.mpr hzl)).1 ((le_max_right ..).trans_lt hh)
    have hfrac : (b-1/2)/((h:ℝ)+1) ≤ z.re-1/2 := (div_le_iff₀ (pos h)).2 (by nlinarith)
    apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid q χ hχ _ _ _ (left h).le
      (right h) hb1 (pos h).le).2 (grids h) z
    exact ⟨⟨by linarith,hzr⟩,abs_le.mp hIm⟩
