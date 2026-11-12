-- Prove2me | solution 1 for FMMM.TSM.min_ratio_eq_alpha
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:42:25.617863+00:00
-- url     : https://prove2.me/submissions/42ca428e-f994-46d7-9f0a-02bb3ef640ed

import Mathlib
import Definitions.Def_FMMM_TSM_alpha

open FMMM.TSM in
theorem solution :
    0 < 5 / 3 - 4 / (3 * Real.exp 1) ∧ 0 < 4 / 3 - 2 / (3 * Real.exp 1) ∧ 0 < 1 - 1 / Real.exp 1 ∧
    (0.735 ≤ (1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)) ∧
      (1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)) < 0.736) ∧
    (0.670 ≤ (1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1)) ∧
      (1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1)) < 0.671) ∧
    (0.709 ≤ (1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1) ∧
      (1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1) < 0.710) ∧
    min (min ((1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)))
        ((1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1))))
      ((1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1)) = alpha := by
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
  obtain ⟨x, hx⟩ : ∃ x, x = 1 / Real.exp 1 := ⟨_, rfl⟩
  have e1 : 1 / Real.exp 2 = x ^ 2 := by rw [he2, hx]; ring
  have e2 : 4 / (3 * Real.exp 1) = 4 / 3 * x := by rw [hx]; ring
  have e3 : 2 / Real.exp 2 = 2 * x ^ 2 := by rw [he2, hx]; ring
  have e4 : 2 / (3 * Real.exp 1) = 2 / 3 * x := by rw [hx]; ring
  have e5 : 3 / (2 * Real.exp 1) = 3 / 2 * x := by rw [hx]; ring
  have hxl : (0.367879441:ℝ) < x := by
    rw [hx, lt_div_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_lt_d9]
  have hxu : x < (0.367879442:ℝ) := by
    rw [hx, div_lt_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  unfold alpha
  rw [e1, e2, e3, e4, e5, ← hx]
  have hD1 : (0:ℝ) < 5 / 3 - 4 / 3 * x := by linarith
  have hD2 : (0:ℝ) < 4 / 3 - 2 / 3 * x := by linarith
  have hD3 : (0:ℝ) < 1 - x := by linarith
  have a1 : (0.735:ℝ) ≤ (1 - x ^ 2) / (5 / 3 - 4 / 3 * x) := by
    rw [le_div_iff₀ hD1]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  have a2 : (1 - x ^ 2) / (5 / 3 - 4 / 3 * x) < (0.736:ℝ) := by
    rw [div_lt_iff₀ hD1]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  have b1 : (0.670:ℝ) ≤ (1 - 2 * x ^ 2) / (4 / 3 - 2 / 3 * x) := by
    rw [le_div_iff₀ hD2]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  have b2 : (1 - 2 * x ^ 2) / (4 / 3 - 2 / 3 * x) < (0.671:ℝ) := by
    rw [div_lt_iff₀ hD2]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  have c1 : (0.709:ℝ) ≤ (1 - 3 / 2 * x) / (1 - x) := by
    rw [le_div_iff₀ hD3]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  have c2 : (1 - 3 / 2 * x) / (1 - x) < (0.710:ℝ) := by
    rw [div_lt_iff₀ hD3]; nlinarith [mul_pos (sub_pos.2 hxl) (sub_pos.2 hxu)]
  refine ⟨hD1, hD2, hD3, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ?_⟩
  have hBA : (1 - 2 * x ^ 2) / (4 / 3 - 2 / 3 * x) ≤ (1 - x ^ 2) / (5 / 3 - 4 / 3 * x) := by
    linarith
  have hBC : (1 - 2 * x ^ 2) / (4 / 3 - 2 / 3 * x) ≤ (1 - 3 / 2 * x) / (1 - x) := by
    linarith
  rw [min_eq_right hBA, min_eq_left hBC]
