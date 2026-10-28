-- Prove2me | solution 1 for D1Bound5.exists_small_normalized_root_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:28.407391+00:00
-- url     : https://prove2.me/submissions/e1e5adbd-560f-4222-babb-d5da975acd08

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_small_root_error

section
namespace D1Bound5



/-- The same choice for normalized off-diagonal entries of an integral
root matrix. Only complex algebra is used at this stage. -/
theorem _root_.solution (a b u v r : ℂ)
    (hu : u^2=a) (hv : v^2=b) (hr : r^2=a*b+1)
    (hab : 9 ≤ ‖a*b‖) :
    ∃ t : ℂ, (t=u*r*v ∨ t=-(u*r*v)) ∧
      ‖t-a*b‖ < (16/31 : ℝ) ∧
      ‖(t-a*b)-(1/2 : ℂ)‖ < (128/8649 : ℝ) := by
  have ht : (u*r*v)^2 = (a*b)*((a*b)+1) := by
    rw [mul_pow,mul_pow,hu,hv,hr]
    ring
  exact exists_small_root_error (a*b) (u*r*v) hab ht








end D1Bound5
end
