-- Prove2me | solution 1 for BitDFT.guarded_output_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:24:20.854985+00:00
-- url     : https://prove2.me/submissions/7195ba14-7e85-4a22-9967-8da26105e246

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_guard_precision_bound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

private lemma value_scale (p n : ℕ) (z : ℤ × ℤ) :
    value p ((n : ℤ) * z.1, (n : ℤ) * z.2) = (n : ℂ) * value p z := by
  simp only [value, Int.cast_mul, Int.cast_natCast]
  ring

theorem solution (n b : ℕ) (hn : 1 ≤ n)
    (X : Fin n → ℂ) (W : Fin n → ℤ × ℤ)
    (hdisc : vectorDisc (guardPrecision n b) W)
    (herr : ∀ k, ulpError (guardPrecision n b) (W k) (ndft X k) < 12 * (n : ℝ)^2) :
    (∀ k, ‖value (guardPrecision n b) ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2)‖ ≤ n) ∧
    (∀ k, ‖value (guardPrecision n b) ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2) - dft X k‖ < ((2 : ℝ)^b)⁻¹) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnzero : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq : (0 : ℝ) < 2 ^ guardPrecision n b := by positivity
  have hb : (0 : ℝ) < 2 ^ b := by positivity
  have hguard : 12 * (n : ℝ)^3 * 2^b < 2^guardPrecision n b := by
    exact_mod_cast BitDFT.guard_precision_bound n b hn
  constructor
  · intro k
    rw [value_scale, norm_mul, Complex.norm_natCast]
    simpa using mul_le_mul_of_nonneg_left (hdisc k) hnpos.le
  · intro k
    have he := herr k
    unfold ulpError at he
    have he' : ‖value (guardPrecision n b) (W k) - ndft X k‖ <
        12 * (n : ℝ)^2 / 2^guardPrecision n b := (lt_div_iff₀ hq).2 (by nlinarith)
    have hid : (n : ℂ) * (value (guardPrecision n b) (W k) - ndft X k) =
        (n : ℂ) * value (guardPrecision n b) (W k) - dft X k := by
      unfold ndft
      field_simp
    rw [value_scale, ← hid, norm_mul, Complex.norm_natCast]
    calc
      (n : ℝ) * ‖value (guardPrecision n b) (W k) - ndft X k‖
        < (n : ℝ) * (12 * (n : ℝ)^2 / 2^guardPrecision n b) := mul_lt_mul_of_pos_left he' hnpos
      _ = (12 * (n : ℝ)^3) / 2^guardPrecision n b := by ring
      _ < ((2 : ℝ)^b)⁻¹ := by
        rw [div_lt_iff₀ hq]
        have hm := mul_lt_mul_of_pos_right hguard (inv_pos.mpr hb)
        simpa [mul_assoc, ne_of_gt hb, mul_comm] using hm
