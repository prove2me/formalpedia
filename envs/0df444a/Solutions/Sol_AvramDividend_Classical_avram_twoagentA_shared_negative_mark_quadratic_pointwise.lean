-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_negative_mark_quadratic_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:40:18.624299+00:00
-- url     : https://prove2.me/submissions/d714e077-1f95-4b21-bd77-9582e3229184

import Mathlib
open Set
noncomputable section
set_option autoImplicit false

theorem solution
    (i : ℕ) (z : ℝ)
    (hz : z ∈ Set.Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) :
    let c : ℝ := -(1 / ((i : ℝ) + 1))
    let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    0 ≤ z - c ∧ z - c ≤ δ ∧ δ ≤ 2 * z ^ 2 ∧ c ^ 2 ≤ 4 * z ^ 2 := by
  rcases hz with ⟨hzlo, hzhi⟩
  let a : ℝ := (i : ℝ) + 1
  let b : ℝ := (i : ℝ) + 2
  let u : ℝ := 1 / b
  let v : ℝ := 1 / a
  have hi : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hu : 0 < u := one_div_pos.mpr hb
  have hv : 0 < v := one_div_pos.mpr ha
  have h2 : v ≤ 2 * u := by
    calc
      v = 1 / a := rfl
      _ ≤ 2 / b := (div_le_div_iff₀ ha hb).mpr (by dsimp [a, b]; nlinarith)
      _ = 2 * u := by dsimp [u]; simp only [div_eq_mul_inv, one_mul]
  have hd : v - u = v * u := by
    dsimp [v, u, a, b]
    field_simp [show ((i : ℝ) + 1) ≠ 0 by positivity,
      show ((i : ℝ) + 2) ≠ 0 by positivity]
    ring
  have hzu : u ≤ -z := by dsimp [u, b]; linarith [hzhi]
  have hleft : 0 ≤ 2 * u - v := by linarith
  have hsmall : u ^ 2 ≤ z ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ -z - u by linarith)
      (show 0 ≤ -z + u by linarith)]
  dsimp only
  simp only [sub_neg_eq_add, neg_sq]
  change 0 ≤ z + v ∧ z + v ≤ v - u ∧
    v - u ≤ 2 * z ^ 2 ∧ v ^ 2 ≤ 4 * z ^ 2
  constructor
  · dsimp [v, a]; linarith [hzlo]
  constructor
  · linarith
  constructor
  · nlinarith [mul_nonneg hleft (le_of_lt hu)]
  · nlinarith [mul_nonneg hleft (show 0 ≤ 2 * u + v by positivity)]
