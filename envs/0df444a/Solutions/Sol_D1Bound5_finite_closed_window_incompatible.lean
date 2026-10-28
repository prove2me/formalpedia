-- Prove2me | solution 1 for D1Bound5.finite_closed_window_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:03.300171+00:00
-- url     : https://prove2.me/submissions/68b8dcb9-0c35-426f-b0e7-8118d532801e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

section
namespace D1Bound5



/-- Both endpoints are excluded: each summand is at most one half inside
the closed window, contradicting the strict inequality from an actual
nonzero integral form. -/
theorem _root_.solution
    (C D Z U V eps : ℝ) (hC : 0 < C) (hZ : 0 < Z)
    (hU : 0 < U) (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hrootlo : (1-eps)*C*D ≤ Z^2) (hroothi : Z^2 ≤ (1+eps)*C*D)
    (hform : 1 < U/Z+V*Z)
    (hlower : 4*U^2/(C*(1-eps)) ≤ D)
    (hupper : D ≤ 1/(4*V^2*C*(1+eps))) : False := by
  have heminus : 0 < 1-eps := sub_pos.mpr heps1
  have heplus : 0 < 1+eps := by linarith
  have hlo := (div_le_iff₀ (mul_pos hC heminus)).1 hlower
  have hsquare : (2*U)^2 ≤ Z^2 := by nlinarith only [hlo, hrootlo]
  have hlinear : 2*U ≤ Z := by
    by_contra h
    have hh : Z < 2*U := lt_of_not_ge h
    have hp := mul_pos (sub_pos.mpr hh) (by positivity : 0 < 2*U+Z)
    nlinarith only [hp, hsquare]
  have hfirst : U/Z ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hZ).2
    linarith only [hlinear]
  have hhi := (le_div_iff₀ (by positivity : 0 < 4*V^2*C*(1+eps))).1 hupper
  have hscaled := mul_le_mul_of_nonneg_left hroothi (by positivity : 0 ≤ 4*V^2)
  have hsq : (2*V*Z)^2 ≤ 1 := by nlinarith only [hhi, hscaled]
  have hsecond : V*Z ≤ (1/2 : ℝ) := by
    have hp : 0 ≤ 2*V*Z := by positivity
    nlinarith only [hsq, hp, sq_nonneg (2*V*Z-1)]
  linarith only [hform, hfirst, hsecond]

end D1Bound5
end
