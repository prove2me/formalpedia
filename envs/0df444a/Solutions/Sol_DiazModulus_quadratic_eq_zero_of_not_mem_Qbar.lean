-- Prove2me | solution 1 for DiazModulus.quadratic_eq_zero_of_not_mem_Qbar
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:17:46.918289+00:00
-- url     : https://prove2.me/submissions/ae85d7f5-96e3-4793-aafa-be3c2d0fba8d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

open DiazModulus in
/-- A root outside `Qbar` of a quadratic with coefficients in `Qbar` forces all three
coefficients to vanish. If `a = 0 ≠ b` then `z = -c/b`; if `a ≠ 0`, completing the square puts
`(2az + b)² = b² - 4ac` in `Qbar`, hence `2az + b` and then `z` too. -/
theorem solution {z a b c : ℂ} (hz : z ∉ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (h : a * z ^ 2 + b * z + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · exact ⟨ha0, hb0, by simpa [ha0, hb0] using h⟩
    · refine absurd ?_ hz
      have hzeq : z = -c / b := by
        field_simp
        linear_combination h - z ^ 2 * ha0
      rw [hzeq]
      exact Subfield.div_mem _ (Subfield.neg_mem _ hc) hb
  · refine absurd ?_ hz
    have hw : (2 * a * z + b) ^ 2 = b ^ 2 - 4 * a * c := by
      linear_combination (4 * a) * h
    have hwQ : (2 * a * z + b) ^ 2 ∈ Qbar := by
      rw [hw]
      exact Subfield.sub_mem _ (Subfield.pow_mem _ hb 2)
        (Subfield.mul_mem _ (Subfield.mul_mem _ (ofNat_mem Qbar 4) ha) hc)
    have hwmem : 2 * a * z + b ∈ Qbar :=
      mem_Qbar_iff.2 ((mem_Qbar_iff.1 hwQ).of_pow (n := 2) (by norm_num))
    have hzeq : z = ((2 * a * z + b) - b) / (2 * a) := by
      field_simp
      ring
    rw [hzeq]
    exact Subfield.div_mem _ (Subfield.sub_mem _ hwmem hb)
      (Subfield.mul_mem _ (ofNat_mem Qbar 2) ha)
