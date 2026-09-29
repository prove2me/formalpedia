-- Prove2me | solution 1 for Freiman.form_orbit_axis_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:16:22.293649+00:00
-- url     : https://prove2.me/submissions/0cb381d6-d1ab-47e0-9543-5d0e92ea6754

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_step_identity

open Freiman

set_option autoImplicit false

private theorem int_square_ge_one (p : ℤ) (hp : p ≠ 0) : (1 : ℝ) ≤ (p : ℝ)^2 := by
  have hs : (1 : ℤ) ≤ p^2 := by
    rcases lt_or_gt_of_ne hp with h | h
    · have hh : p ≤ -1 := by omega
      nlinarith
    · have hh : 1 ≤ p := by omega
      nlinarith
  exact_mod_cast hs

theorem solution (R : ReducedOrbit) (n p q : ℤ)
    (hpq : p ≠ 0 ∨ q ≠ 0) (haxis : p = 0 ∨ q = 0) :
    orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  have hrecpos (i : ℤ) : 0 < 1 / (R.alpha i + R.beta i) := by
    apply one_div_pos.mpr
    linarith [R.alpha_gt i, R.beta_pos i]
  have hbdd : BddBelow (Set.range (fun i : ℤ => 1 / (R.alpha i + R.beta i))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨i, rfl⟩
    exact (hrecpos i).le
  have hinf (i : ℤ) : orbitReciprocalInfimum R ≤ 1 / (R.alpha i + R.beta i) :=
    csInf_le hbdd ⟨i, rfl⟩
  have hunit (i : ℤ) : |reducedValue (R.alpha i) (R.beta i) 1 0| =
      1 / (R.alpha i + R.beta i) := by
    simp only [reducedValue, quadraticValue, Int.cast_one, Int.cast_zero, one_pow,
      zero_pow (by norm_num : 2 ≠ 0), mul_one, mul_zero, add_zero, reducedA]
    exact abs_of_pos (hrecpos i)
  have hunit' : |reducedValue (R.alpha n) (R.beta n) 0 1| =
      1 / (R.alpha (n - 1) + R.beta (n - 1)) := by
    have he := form_step_identity R (n - 1) 0 1
    simp only [mul_zero, zero_add, sub_add_cancel] at he
    rw [← hunit (n - 1), he, abs_neg]
  rcases haxis with rfl | rfl
  · have hq : q ≠ 0 := hpq.resolve_left (by simp)
    have he : reducedValue (R.alpha n) (R.beta n) 0 q =
        (q : ℝ)^2 * reducedValue (R.alpha n) (R.beta n) 0 1 := by
      simp [reducedValue, quadraticValue]
      <;> ring
    rw [he, abs_mul, abs_sq, hunit']
    exact (hinf (n - 1)).trans (le_mul_of_one_le_left (hrecpos (n - 1)).le (int_square_ge_one q hq))
  · have hp : p ≠ 0 := hpq.resolve_right (by simp)
    have he : reducedValue (R.alpha n) (R.beta n) p 0 =
        (p : ℝ)^2 * reducedValue (R.alpha n) (R.beta n) 1 0 := by
      simp [reducedValue, quadraticValue]
      <;> ring
    rw [he, abs_mul, abs_sq, hunit]
    exact (hinf n).trans (le_mul_of_one_le_left (hrecpos n).le (int_square_ge_one p hp))
