-- Prove2me | solution 1 for D1Bound5.bennett_two_distance_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:14.940064+00:00
-- url     : https://prove2.me/submissions/a2e452e0-8865-4483-ad00-ca71898cb1fd

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5





/-- Triangle geometry controls the same rational factor as in the paper.
The assumptions hold for u=min(A,delta), v=max(A,delta), and A≤B. -/
theorem _root_.solution (B u v : ℝ)
    (hB : 0 < B) (hu : 0 < u) (huB : u ≤ B)
    (huv : u ≤ v) (hvB : v ≤ u + B) :
    v ^ 2 / (v - 2 * u / 5) ≤ (5 / 2 : ℝ) * B := by
  have hd : 0 < v - 2 * u / 5 := by linarith
  apply (div_le_iff₀ hd).mpr
  have hprod : 0 ≤ (v - u) * (u + B - v) :=
    mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hvB)
  by_cases hsmall : u ≤ 3 * B / 4
  · have hp : 0 ≤ (3 * B / 2 - 2 * u) * v :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg u]
  · have hp : 0 ≤ (2 * u - 3 * B / 2) * (u + B - v) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hvB)
    have hgap : 0 ≤ (B - u) * (3 * B + 2 * u) :=
      mul_nonneg (sub_nonneg.mpr huB) (by positivity)
    nlinarith





end D1Bound5
end
