-- Prove2me | solution 1 for DataDrivenRO.FwdBwd.lambda_star
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:41:33.654932+00:00
-- url     : https://prove2.me/submissions/d60fffc7-3f29-45cd-b8b3-400c638f3685

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

set_option autoImplicit false

namespace LambdaStar8c

theorem lower (L S lam : ℝ) (hL : 0 < L) (hS : 0 ≤ S) (hlam : 0 < lam) :
    Real.sqrt (2 * L * S) ≤ lam * L + S / (2 * lam) := by
  set a := Real.sqrt (2 * L * S) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * L * S := Real.sq_sqrt (by positivity)
  rw [show lam * L + S / (2 * lam) = (2 * L * lam ^ 2 + S) / (2 * lam) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  have key : 0 ≤ 2 * L * (2 * L * lam ^ 2 + S - a * (2 * lam)) := by
    nlinarith [sq_nonneg (2 * L * lam - a)]
  have := (mul_nonneg_iff_of_pos_left (by linarith : (0:ℝ) < 2 * L)).mp key
  linarith

theorem attain (L S : ℝ) (hL : 0 < L) (hS : 0 < S) :
    0 < Real.sqrt (S / (2 * L)) ∧
      Real.sqrt (S / (2 * L)) * L + S / (2 * Real.sqrt (S / (2 * L))) =
        Real.sqrt (2 * L * S) := by
  set m := Real.sqrt (S / (2 * L)) with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr (by positivity)
  have hm2 : m ^ 2 = S / (2 * L) := Real.sq_sqrt (by positivity)
  refine ⟨hm0, ?_⟩
  have hS' : S = 2 * L * m ^ 2 := by rw [hm2]; field_simp
  have e1 : m * L + S / (2 * m) = 2 * L * m := by
    rw [hS']; field_simp; ring
  rw [e1]
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  rw [hS']; ring

end LambdaStar8c

open DataDrivenRO.FwdBwd in
theorem solution (L S : ℝ) (hL : 0 < L) (hS : 0 ≤ S) :
    IsGLB ((fun lam : ℝ => lam * L + S / (2 * lam)) '' Set.Ioi 0) (Real.sqrt (2 * L * S)) ∧
    (0 < S → 0 < Real.sqrt (S / (2 * L)) ∧
      Real.sqrt (S / (2 * L)) * L + S / (2 * Real.sqrt (S / (2 * L))) =
        Real.sqrt (2 * L * S)) := by
  refine ⟨⟨?_, ?_⟩, fun h => LambdaStar8c.attain L S hL h⟩
  · rintro _ ⟨lam, hlam, rfl⟩
    exact LambdaStar8c.lower L S lam hL hS hlam
  · intro b hb
    rcases hS.lt_or_eq with hpos | hzero
    · obtain ⟨h1, h2⟩ := LambdaStar8c.attain L S hL hpos
      rw [← h2]
      exact hb ⟨_, h1, rfl⟩
    · subst hzero
      simp only [mul_zero, Real.sqrt_zero]
      by_contra hb0
      have hb0 : 0 < b := not_le.mp hb0
      have hmem := hb ⟨b / (2 * L), (by positivity : (0:ℝ) < b / (2 * L)), rfl⟩
      simp only [zero_div, add_zero] at hmem
      have : b / (2 * L) * L = b / 2 := by field_simp
      linarith
