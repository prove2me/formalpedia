-- Prove2me | solution 1 for BookProof.YangMillsFriedrichsLimit.memLp_one_div_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:56:36.469531+00:00
-- url     : https://prove2.me/submissions/4cdcd66b-0068-467c-bf8f-475085269cbe

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.memℓp_one_div_succ
open BookProof.YangMillsFriedrichsLimit



open BookProof.FarisLavine BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem solution : Memℓp (fun n : ℕ => (1 / (n + 1) : ℂ)) 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine memℓp_gen ?_
  have h : (fun n : ℕ => ‖(1 / (n + 1) : ℂ)‖ ^ (2 : ENNReal).toReal) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    funext n
    rw [show (2 : ENNReal).toReal = (2 : ℕ) by norm_num, Real.rpow_natCast, norm_div, norm_one]
    rw [Nat.cast_add, Nat.cast_one]
    rw [show ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
    rw [div_pow, one_pow]
  rw [h]
  exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
