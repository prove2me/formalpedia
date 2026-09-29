-- Prove2me | solution 1 for Freiman.upper_tree_cylinder_width
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:12:57.631702+00:00
-- url     : https://prove2.me/submissions/60ba6744-8be9-4b6f-896e-fb31daae985b

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman

private theorem row_endpoints (k : Fin 5) :
    (upperRows k).parent.left ∈ Set.Icc (0 : ℝ) 1 ∧
    (upperRows k).parent.right ∈ Set.Icc (0 : ℝ) 1 := by
  have hs0 := Real.sqrt_nonneg (21 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hlo : (4 : ℝ) < Real.sqrt 21 := by nlinarith
  have hhi : Real.sqrt 21 < (5 : ℝ) := by nlinarith
  have h1 : upperTheta1 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta1]; constructor <;> nlinarith
  have h3 : upperTheta3 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta3]; constructor <;> nlinarith
  have h5 : upperTheta5 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta5]; constructor <;> nlinarith
  have h6 : upperTheta6 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta6]; constructor <;> nlinarith
  have h8 : upperTheta8 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta8]; constructor <;> nlinarith
  fin_cases k
  · exact ⟨h8, h1⟩
  · exact ⟨h8, h3⟩
  · exact ⟨h8, h5⟩
  · exact ⟨h6, h1⟩
  · exact ⟨h6, h3⟩

theorem solution (p : List ℕ+) (k : Fin 5) (w : List Bool) :
    upperLength (upperTree p k w) ≤
    1 / (((Nat.fib ((upperStateAt ⟨p, k⟩ w).word.length + 1) : ℕ) : ℝ) ^ 2) := by
  let s := upperStateAt ⟨p, k⟩ w
  have h := prefixEval_cylinder_bound s.word (upperRows s.row).parent.left
    (upperRows s.row).parent.right (row_endpoints s.row).1 (row_endpoints s.row).2
  change max (prefixEval s.word (upperRows s.row).parent.left)
      (prefixEval s.word (upperRows s.row).parent.right) -
    min (prefixEval s.word (upperRows s.row).parent.left)
      (prefixEval s.word (upperRows s.row).parent.right) ≤ _
  rw [max_sub_min_eq_abs, abs_sub_comm]
  exact h
