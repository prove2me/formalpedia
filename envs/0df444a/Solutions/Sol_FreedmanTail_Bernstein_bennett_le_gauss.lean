-- Prove2me | solution 1 for FreedmanTail.Bernstein.bennett_le_gauss
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:23:26.076134+00:00
-- url     : https://prove2.me/submissions/ce8c6b58-cbc8-420c-84cf-a1ad842c9381

import Mathlib

private lemma log_bound (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y => Real.log (1 - y) + y + y ^ 2 / 2
  have hd : ∀ y ∈ Set.Icc 0 x, HasDerivAt f (-1 / (1 - y) + 1 + y) y := by
    intro y hy
    have hne : 1 - y ≠ 0 := by linarith [hy.2]
    convert (((Real.hasDerivAt_log hne).comp y ((hasDerivAt_const y 1).sub (hasDerivAt_id y))).add
      (hasDerivAt_id y)).add (((hasDerivAt_id y).pow 2).div_const 2) using 1
    all_goals first | rfl | (dsimp [id]; ring) | (funext z; dsimp [f]; ring)
  have hm : AntitoneOn f (Set.Icc 0 x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 x)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' := interior_subset hy
      rw [(hd y hy').deriv]
      have hpos : 0 < 1 - y := by linarith [hy'.2]
      convert (show -(y ^ 2) / (1 - y) ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg y]) hpos.le) using 1 <;> field_simp <;> ring
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  dsimp [f] at hh
  simp only [sub_zero, Real.log_one, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at hh
  linarith

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  have hs : 0 < a + b := by positivity
  have he : b / (a + b) = 1 - a / (a + b) := by field_simp; ring
  have hl := log_bound (a / (a + b)) (by positivity) ((div_lt_one hs).mpr (by linarith))
  rw [← he] at hl
  rw [Real.rpow_def_of_pos (div_pos hb hs), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl hs.le
  have halg : (a + b) * (- (a / (a + b)) - (a / (a + b)) ^ 2 / 2) + a = -(a ^ 2) / (2 * (a + b)) := by
    field_simp
    ring
  nlinarith [halg]

#print axioms solution
