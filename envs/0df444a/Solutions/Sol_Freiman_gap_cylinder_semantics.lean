-- Prove2me | solution 1 for Freiman.gap_cylinder_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:07.982858+00:00
-- url     : https://prove2.me/submissions/e4e503d2-21d1-4a94-b051-2c4e2d8d5685

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_cylinder_decomposition
import Theorems.Thm_Freiman_gap_tail_interior
import Theorems.Thm_Freiman_gap_prefix_rat_interval

open Freiman

theorem solution (a : ℤ → ℕ+) (i : ℤ) (s : GapState) (j : ℕ) (hd : gapDigits a) (hm : gapMatch a i s) (hj : j < s.word.length) : (gapCylinderLower s.word j : ℝ) < localValue a (i+(j : ℤ)-(s.centre : ℤ)) ∧ localValue a (i+(j : ℤ)-(s.centre : ℤ)) < (gapCylinderUpper s.word j : ℝ) := by
  have hl := gap_prefix_rat_interval ((s.word.take j).reverse) _ (gap_tail_interior (fun n : ℕ => a (i-(s.centre : ℤ)-(n : ℤ)-1)) (fun n => hd _))
  have hr := gap_prefix_rat_interval (s.word.drop (j+1)) _ (gap_tail_interior (fun n : ℕ => a (i+(s.word.length : ℤ)-(s.centre : ℤ)+(n : ℤ))) (fun n => hd _))
  rw [gap_cylinder_decomposition a i s j hm hj]
  dsimp only [gapCylinderLower,gapCylinderUpper]
  push_cast
  constructor <;> linarith [hl.1,hl.2,hr.1,hr.2]
