-- Prove2me | solution 1 for D1Bound5.exists_frontier_root_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:13.060151+00:00
-- url     : https://prove2.me/submissions/269b1ce5-515d-4df3-9124-cab4e495a7ee

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_root_error_control

section
namespace D1Bound5

/-- A uniform sign choice for |x|>=5 gives the variable frontier error
1/(7|x|). The rational margin32/225<1/7 avoids analytic square roots. -/
theorem _root_.solution (x t : ℂ)
    (hx : 5 ≤ ‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧
      ‖(v-x)-(1/2 : ℂ)‖ ≤ 1/(7*‖x‖) := by
  have hx0 : 0 < ‖x‖ := by linarith only [hx]
  have hgap : 1 < (1-(7/8 : ℝ)^2)*‖x‖ := by nlinarith only [hx]
  obtain ⟨v,hv,_,hhalf⟩ := exists_root_error_control x t (7/8)
    (by norm_num) hx0 hgap ht
  refine ⟨v,hv,le_of_lt ?_⟩
  apply (lt_div_iff₀ (by positivity : 0 < 7*‖x‖)).mpr
  nlinarith only [hhalf]









end D1Bound5
end
