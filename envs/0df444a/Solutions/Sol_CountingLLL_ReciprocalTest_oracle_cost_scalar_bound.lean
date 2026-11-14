-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.oracle_cost_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:12:54.11139+00:00
-- url     : https://prove2.me/submissions/3dd24691-a9bd-46b1-85df-37ff4b59abb1

import Mathlib
set_option autoImplicit false

theorem solution (u M : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 33/80)
    (hM0 : 0 ≤ M) (hM : M ≤ 74/25) :
    1-u+(1-u)^2/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by
  let d := 1-u+u^2
  let a := (1-u)^2/d
  have hv : 0 ≤ 1-u := by linarith
  have hd : 0 < d := by dsimp [d]; nlinarith [sq_nonneg u]
  have hda : 1-u ≤ d := by dsimp [d]; nlinarith [sq_nonneg u]
  have ha0 : 0 ≤ a := div_nonneg (sq_nonneg _) (le_of_lt hd)
  have ha : a ≤ 1-u := by
    apply (div_le_iff₀ hd).2
    dsimp [d]
    nlinarith [sq_nonneg u, mul_nonneg hv (sq_nonneg u)]
  have hg : a ≤ d := le_trans ha hda
  have hr : a * (u/d) ≤ u := by
    rw [← mul_div_assoc, div_le_iff₀ hd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg) hu0]
  have hfirst : a*(1-u) ≤ (1-u)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hv]
  have hsecond : (a*(u/d))*M ≤ u*M := mul_le_mul_of_nonneg_right hr hM0
  have hs : u*M ≤ u*(74/25) := mul_le_mul_of_nonneg_left hM hu0
  have hp : u^2 ≤ (33/80 : ℝ)^2 := by nlinarith [sq_nonneg (u+(33/80))]
  have hf : 1-u+(1-u)^2 + u*(74/25) < (3:ℝ) := by nlinarith
  change 1-u+a*(1-u+(u/d)*M) < 3
  nlinarith
