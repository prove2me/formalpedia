-- Prove2me | solution 1 for D1Bound5.finite_tuple_root_relative_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:02.438997+00:00
-- url     : https://prove2.me/submissions/4d3dc74a-2f88-44e7-adfd-d7d3e531d63d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

section
namespace D1Bound5

/-- An actual square root of cd+1 has the relative terminal norm bounds
needed for closed forbidden intervals once |cd|≥4000. -/
theorem _root_.solution
    (c d z : ℂ) (hz : z^2 = c*d+1) (hCD : 4000 ≤ ‖c‖*‖d‖) :
    (1-1/4000 : ℝ)*‖c‖*‖d‖ ≤ ‖z‖^2 ∧
      ‖z‖^2 ≤ (1+1/4000 : ℝ)*‖c‖*‖d‖ := by
  have hsquare : ‖z‖^2 = ‖c*d+1‖ := by rw [← norm_pow, hz]
  have hhi := norm_add_le (c*d) (1 : ℂ)
  have hlo := norm_sub_le (c*d+1) (1 : ℂ)
  simp only [norm_mul, norm_one] at hhi
  simp only [add_sub_cancel_right, norm_mul, norm_one] at hlo
  have herr : 1 ≤ (1/4000 : ℝ)*‖c‖*‖d‖ := by nlinarith only [hCD]
  constructor <;> rw [hsquare] <;> nlinarith only [hhi, hlo, herr]



end D1Bound5
end
