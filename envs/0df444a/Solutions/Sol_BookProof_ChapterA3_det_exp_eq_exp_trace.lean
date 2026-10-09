-- Prove2me | solution 1 for BookProof.ChapterA3.det_exp_eq_exp_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:55.619225+00:00
-- url     : https://prove2.me/submissions/9b38600f-d4d9-4677-9dd5-59b3c0d1bebb

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.det_exp_eq_exp_trace
import Mathlib
import Definitions.Def_ChapterA3f
import Theorems.Thm_BookProof_ChapterA3_hasDerivAt_detExpPath
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp A).det = Real.exp A.trace := by

  -- Define `g : ℝ → ℝ`, `g t := detExpPath A t * Real.exp (-(A.trace * t))`.
  set g : ℝ → ℝ := fun t => detExpPath A t * Real.exp (-(A.trace * t));
  -- By definition of $g$, we know that its derivative is zero everywhere.
  have hg_deriv_zero : ∀ t, HasDerivAt g 0 t := by
    intro t;
    convert HasDerivAt.mul ( hasDerivAt_detExpPath A t ) ( HasDerivAt.exp ( HasDerivAt.neg (
        HasDerivAt.const_mul ( A.trace ) ( hasDerivAt_id t ) ) ) ) using 1 <;>
      (first | rfl | ring | simp +zetaDelta | norm_num)
  -- Since $g$ is differentiable and its derivative is zero everywhere, $g$ must be constant.
  have hg_const : ∀ t₁ t₂, g t₁ = g t₂ := by
    exact fun t₁ t₂ => is_const_of_deriv_eq_zero ( fun t => HasDerivAt.differentiableAt (
        hg_deriv_zero t ) ) ( fun t => HasDerivAt.deriv ( hg_deriv_zero t ) ) t₁ t₂;
  convert congr_arg ( fun x => x / Real.exp ( - ( A.trace * 1 ) ) ) ( hg_const 1 0 ) using 1 <;>
      norm_num [ Real.exp_neg ];
  · simp? +zetaDelta at *;
    unfold detExpPath; norm_num [ mul_assoc, ← Real.exp_add ] ;
  · simp +zetaDelta at *
