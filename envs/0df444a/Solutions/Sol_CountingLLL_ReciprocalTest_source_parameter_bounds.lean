-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.source_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:48:32.048971+00:00
-- url     : https://prove2.me/submissions/2b32d33d-f811-4ac3-bdfd-f768109067b9

import Mathlib

set_option autoImplicit false

open Real

private theorem ex_lower : (94/127 : ℝ) < Real.exp (-(3/10 : ℝ)) := by
  have hx := Real.add_one_le_exp (-(1/200 : ℝ))
  have hp : (199/200 : ℝ)^60 ≤ (Real.exp (-(1/200 : ℝ)))^60 := by
    apply pow_le_pow_left₀ <;> linarith
  have he : (Real.exp (-(1/200 : ℝ)))^60 = Real.exp (-(3/10 : ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at hp
  norm_num at hp ⊢
  linarith

theorem solution (B : ℝ) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) (hB1 : B ≤ 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 := by
  dsimp
  have hB0 : (94/127 : ℝ) < B := lt_of_lt_of_le ex_lower hB
  have hd : 0 < 2-B := by linarith
  have hu0 : 0 ≤ 2*(1-B)/(2-B) := div_nonneg (by linarith) (le_of_lt hd)
  have hu1 : 2*(1-B)/(2-B) < (33/80 : ℝ) := by
    apply (div_lt_iff₀ hd).2
    linarith
  let u := 2*(1-B)/(2-B)
  change 0 ≤ u ∧ u < 33/80 ∧ 0 ≤ u^2/(1-u+u^2) ∧ u^2/(1-u+u^2) < 9/40
  have hu0' : 0 ≤ u := hu0
  have hu1' : u < 33/80 := hu1
  have hden : 0 < 1-u+u^2 := by nlinarith [sq_nonneg u]
  refine ⟨hu0, hu1, div_nonneg (sq_nonneg u) (le_of_lt hden), ?_⟩
  apply (div_lt_iff₀ hden).2
  have hs : u^2 < (33/80 : ℝ)^2 := by nlinarith [sq_nonneg (u+(33/80))]
  nlinarith
