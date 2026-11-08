-- Prove2me | solution 1 for EllipsoidFitting.claim_3_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:24:06.526035+00:00
-- url     : https://prove2.me/submissions/56db739a-0f76-4f22-a24b-392b5c92899f

import Mathlib

set_option autoImplicit false

theorem solution (γ C : ℝ) (hC : C ≠ 0) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) :
    (1 - γ) / γ <
      Real.sqrt ((1 - γ) / γ * (1 / C ^ 2) * (1 - (1 - γ) / γ * (1 - C ^ 2))) := by
  have hγ0 : 0 < γ := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (1 - γ) / γ := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; exact div_pos (by linarith) hγ0
  have ha1 : a < 1 := by rw [ha, div_lt_one hγ0]; linarith
  have hC2 : 0 < C ^ 2 := lt_of_le_of_ne (sq_nonneg C) (Ne.symm (pow_ne_zero 2 hC))
  rw [Real.lt_sqrt ha0.le]
  have e : a * (1 / C ^ 2) * (1 - a * (1 - C ^ 2)) = a ^ 2 + a * (1 - a) / C ^ 2 := by
    field_simp <;> ring
  rw [e]
  have : 0 < a * (1 - a) / C ^ 2 := div_pos (mul_pos ha0 (by linarith)) hC2
  linarith
