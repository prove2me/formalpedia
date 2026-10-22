-- Prove2me | solution 2 for GDGen3.ell_root_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:58:04.025335+00:00
-- url     : https://prove2.me/submissions/f4a96409-a60d-432c-8676-26b8413f8153

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_Abar_root_pos
import Theorems.Thm_GDGen3_Abar_root_step
import Theorems.Thm_GDGen3_D_root_nonneg
import Theorems.Thm_GDGen3_D_root_step

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i j : ℕ)
    (hiN : i ≤ N) (hjN : j ≤ N) (hij : i ≠ j)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 ≤ ell r (rootXi r N) N i j := by
  have hA : ∀ a, a < N → 0 ≤ Abar (rootXi r N) a - Am (rootXi r N) a := by
    intro a ha
    by_cases h0 : a = 0
    · subst a; simp [Abar, Am]
    · simp only [Am, if_neg h0]
      exact le_of_lt (sub_pos.mpr (Abar_root_step r hr hr1 N a (by omega) ha hbranch))
  have hD : ∀ b, 1 ≤ b → b ≤ N → 0 ≤ D r (rootXi r N) N b - D r (rootXi r N) N (b + 1) := by
    intro b hb hbN
    by_cases he : b = N
    · subst b
      have hn1 : D r (rootXi r N) N (N + 1) = 0 := by simp [D]
      rw [hn1, sub_zero]
      exact D_root_nonneg r hr hr1 N N
    · exact le_of_lt (sub_pos.mpr (D_root_step r hr hr1 N b hb (by omega) hbranch))
  unfold ell
  by_cases h : i < j
  · rw [if_pos h]
    apply mul_nonneg (hA i (by omega))
    exact add_nonneg (D_root_nonneg r hr hr1 N j)
      (mul_nonneg (le_of_lt hr) (D_root_nonneg r hr hr1 N (j + 1)))
  · rw [if_neg h]
    have hji : j < i := by omega
    apply mul_nonneg _ (hD i (by omega) hiN)
    apply add_nonneg
    · unfold Am; split_ifs
      · exact le_rfl
      · exact le_of_lt (Abar_root_pos r hr hr1 N (j - 1))
    · exact mul_nonneg (le_of_lt hr) (le_of_lt (Abar_root_pos r hr hr1 N j))
