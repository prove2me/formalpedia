-- Prove2me | solution 1 for Freiman.form_second_root_eventually_reduced
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:07:34.853004+00:00
-- url     : https://prove2.me/submissions/aa687e96-5bc5-4674-b664-7e150e794352

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData

open Freiman

set_option autoImplicit false

theorem solution (r s : ℝ) (hrs : s < r) (D : RootConvergentData r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → secondRootCoordinate D s n ∈ Set.Ioo (-1 : ℝ) 0 := by
  have hδ : 0 < r - s := sub_pos.mpr hrs
  obtain ⟨N₁, hN₁⟩ := D.error_zero ((r - s) / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := D.denominator_difference_escape 1
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have he := abs_lt.mp (hN₁ n (le_trans (le_max_left _ _) hn))
  have he' := abs_lt.mp (hN₁ (n + 1) (by omega))
  have hdiff := hN₂ n (le_trans (le_max_right _ _) hn)
  have hq : (1 : ℝ) ≤ D.q n := by exact_mod_cast D.q_pos n
  have hqδ : r - s ≤ (r - s) * (D.q n : ℝ) := by nlinarith
  have hdiffδ : r - s ≤ (r - s) * ((D.q (n + 1) : ℝ) - D.q n) := by nlinarith
  have hA : 0 < (D.p n : ℝ) - s * (D.q n : ℝ) := by nlinarith [he.1]
  have hAB : (D.p n : ℝ) - s * (D.q n : ℝ) <
      (D.p (n + 1) : ℝ) - s * (D.q (n + 1) : ℝ) := by nlinarith [he.2, he'.1]
  have hden : s * (D.q (n + 1) : ℝ) - D.p (n + 1) < 0 := by linarith
  change -1 < ((D.p n : ℝ) - s * (D.q n : ℝ)) /
      (s * (D.q (n + 1) : ℝ) - D.p (n + 1)) ∧
    ((D.p n : ℝ) - s * (D.q n : ℝ)) /
      (s * (D.q (n + 1) : ℝ) - D.p (n + 1)) < 0
  constructor
  · apply (lt_div_iff_of_neg hden).2
    linarith
  · exact div_neg_of_pos_of_neg hA hden
