-- Prove2me | solution 1 for GeneralCK.B_H_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:58:03.728158+00:00
-- url     : https://prove2.me/submissions/c6fff721-e60b-4a6d-ae37-aeb177baddd4

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman
import Theorems.Thm_GeneralCK_H_strictMonoOn
import Theorems.Thm_GeneralCK_entropyInverse_H_lower
import Theorems.Thm_GeneralCK_eta_one
import Theorems.Thm_GeneralCK_radialContact_H_lower

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)



@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h









end GeneralCK

open GeneralCK
theorem solution {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1 / 2) : B m (H m) = 0 := by
  by_cases heq : m = 1 / 2
  · subst m
    norm_num [B, phi, psi, F, eta_one]
  · have hlt : m < 1 / 2 := lt_of_le_of_ne hm' heq
    have hH : H m < 1 := by
      calc H m < H (1 / 2) := H_strictMonoOn ⟨hm.le, hm'⟩ ⟨by norm_num, le_rfl⟩ hlt
           _ = 1 := H_half
    have hz : |1 - 2 * m| = 1 - 2 * m := abs_of_pos (by linarith)
    have hz' : 1 - 2 * m ≠ 0 := by linarith
    simp [B, phi, psi, eta, ne_of_lt hH, entropyInverse_H_lower hm.le hm',
      hz, F, hz', radialContact_H_lower hm hlt]
