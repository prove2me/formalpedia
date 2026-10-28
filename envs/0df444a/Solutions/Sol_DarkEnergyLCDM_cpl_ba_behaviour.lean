-- Prove2me | solution 1 for DarkEnergyLCDM.cpl_ba_behaviour
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:13:56.369568+00:00
-- url     : https://prove2.me/submissions/ca8af2bc-497f-403e-9b77-0d279349e055

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Filter
open DarkEnergyLCDM

theorem solution (w₀ wₐ : ℝ) :
    (0 < wₐ → Tendsto (fun a => cplEOS w₀ wₐ a) atTop atBot) ∧
    (∃ M : ℝ, ∀ a : ℝ, 0 < a → |baEOS w₀ wₐ a| ≤ M) := by
  refine ⟨fun h => ?_, ⟨|w₀| + 2 * |wₐ|, fun a _ => ?_⟩⟩
  · unfold cplEOS
    have : Tendsto (fun a : ℝ => (1 - a) * wₐ) atTop atBot := by
      have h1 : Tendsto (fun a : ℝ => 1 - a) atTop atBot :=
        tendsto_atBot_add_const_left _ (1:ℝ) tendsto_neg_atTop_atBot |>.congr (fun a => by ring)
      exact h1.atBot_mul_const h
    exact tendsto_atBot_add_const_left _ _ this
  · unfold baEOS
    have hd : 0 < a ^ 2 + (1 - a) ^ 2 := by nlinarith [sq_nonneg (a - 1/2)]
    have hq : |(1 - a) / (a ^ 2 + (1 - a) ^ 2)| ≤ 2 := by
      rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
      rcases le_total 0 (1 - a) with h | h
      · rw [abs_of_nonneg h]; nlinarith [sq_nonneg (a - 1/2), sq_nonneg (2*(1-a) - 5/4)]
      · rw [abs_of_nonpos h]; nlinarith [sq_nonneg (a - 1/2)]
    calc |w₀ + wₐ * ((1 - a) / (a ^ 2 + (1 - a) ^ 2))|
        ≤ |w₀| + |wₐ| * |(1 - a) / (a ^ 2 + (1 - a) ^ 2)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |w₀| + |wₐ| * 2 := by gcongr
      _ = _ := by ring
