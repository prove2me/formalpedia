-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.source_accuracy_algebra
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:16:00.16928+00:00
-- url     : https://prove2.me/submissions/18909603-c2ed-427a-b174-84073d86ca15

import Mathlib
set_option autoImplicit false

private theorem abstract_algebra (u θ : ℝ) (hθ : θ ≠ 0) (hθ1 : 1-θ ≠ 0) :
    1-((1-u)*(1-θ/(2*(1-θ))) + u*((1-θ/(2*(1-θ)))-1+θ)/θ)/2 =
      1/2+((1-u)*θ+u)/(4*(1-θ)) := by
  field_simp
  <;> ring

theorem solution (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let I := 1-θ/(2*(1-θ))
    1-((1-u)*I + u*(I-1+θ)/θ)/2 = 1/(2*B) := by
  let u : ℝ := 2*(1-B)/(2-B)
  let d : ℝ := 1-u+u^2
  let θ : ℝ := u^2/d
  have hdB : 0 < 2-B := by linarith
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    apply (div_lt_one hdB).2
    linarith
  have hd : 0 < d := by dsimp [d]; nlinarith [sq_nonneg u]
  have hθ : θ ≠ 0 := div_ne_zero (pow_ne_zero _ (ne_of_gt hu0)) (ne_of_gt hd)
  have hθ1 : 1-θ ≠ 0 := by
    apply ne_of_gt
    dsimp [θ]
    rw [sub_pos, div_lt_one hd]
    dsimp [d]
    linarith
  change 1-((1-u)*(1-θ/(2*(1-θ))) + u*((1-θ/(2*(1-θ)))-1+θ)/θ)/2 = 1/(2*B)
  rw [abstract_algebra u θ hθ hθ1]
  have hstep : 1/2+((1-u)*θ+u)/(4*(1-θ)) = (2-u)/(4*(1-u)) := by
    have hinner : 1 - u^2/(1-u+u^2) ≠ 0 := by simpa [θ,d] using hθ1
    have hdd : 1-u+u^2 ≠ 0 := by simpa [d] using ne_of_gt hd
    have h1u : 1-u ≠ 0 := by linarith
    dsimp [θ, d]
    field_simp [hinner, hdd, h1u]
    <;> ring
  rw [hstep]
  have h1u : 1-2*(1-B)/(2-B) ≠ 0 := by dsimp [u] at hu1; linarith
  dsimp [u]
  field_simp [h1u, ne_of_gt hdB, ne_of_gt hB0]
  <;> ring_nf
  <;> field_simp [ne_of_gt hB0]
