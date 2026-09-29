-- Prove2me | solution 1 for Diaz.no_vanishing_coeff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:15.698349+00:00
-- url     : https://prove2.me/submissions/e72b19c4-1c83-43c6-8138-be76cfec8fb6

import Mathlib

namespace Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

/-- The coefficient `wᵀ H v` factors, because `H` has rank one. -/
theorem coeff_factor (hu0 : u ≠ 0) (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) :
    w 0 * (u * v 0 + r * v 1) + w 1 * (r * v 0 + conj u * v 1)
      = (w 0 + (r / u) * w 1) * (u * v 0 + r * v 1) := by
  have hc : conj u = r ^ 2 / u := by
    rw [eq_div_iff hu0]; linear_combination h
  rw [hc]; field_simp
end

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

/-- If `u * a + r * b = 0` with `a, b` in `K`, not both zero, and `r ≠ 0`
in `K`, then `u ∈ K`. -/
theorem mem_of_lin_rel (hr : r ∈ K) (hr0 : r ≠ 0) {a b : ℂ}
    (ha : a ∈ K) (hb : b ∈ K) (hab : ¬ (a = 0 ∧ b = 0))
    (h : u * a + r * b = 0) : u ∈ K := by
  by_cases ha0 : a = 0
  · exfalso
    rw [ha0, mul_zero, zero_add] at h
    exact hab ⟨ha0, by simpa [hr0] using mul_eq_zero.mp h⟩
  · have : u = -(r * b) / a := by
      rw [eq_div_iff ha0]; linear_combination h
    rw [this]
    exact div_mem (neg_mem (mul_mem hr hb)) ha
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- An element outside a subfield is non-zero, subfields containing `0`. -/
theorem ne_zero_of_notMem {K : Subfield ℂ} {z : ℂ} (h : z ∉ K) : z ≠ 0 := by
  rintro rfl
  exact h K.zero_mem
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

open Diaz in
theorem solution (hr : r ∈ K) (huK : u ∉ K)
    (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ K) (hvK : ∀ i, v i ∈ K)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    w 0 * (u * v 0 + r * v 1) + w 1 * (r * v 0 + conj u * v 1) ≠ 0 := by
  have hu0 : u ≠ 0 := ne_zero_of_notMem huK
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hz : u * conj u = 0 := by simpa using h
    rcases mul_eq_zero.mp hz with h' | h'
    · exact hu0 h'
    · exact hu0 (by simpa using h')
  rw [coeff_factor hu0 h]
  intro hzero
  rcases mul_eq_zero.mp hzero with hfac | hfac
  · -- `w 0 + (r/u) * w 1 = 0`, i.e. `u * w 0 + r * w 1 = 0`
    have h' : u * w 0 + r * w 1 = 0 := by
      field_simp at hfac; linear_combination hfac
    refine huK (mem_of_lin_rel hr hr0 (hwK 0) (hwK 1) ?_ h')
    rintro ⟨h0, h1⟩
    exact hw (funext fun i => by fin_cases i <;> assumption)
  · -- `u * v 0 + r * v 1 = 0`
    refine huK (mem_of_lin_rel hr hr0 (hvK 0) (hvK 1) ?_ hfac)
    rintro ⟨h0, h1⟩
    exact hv (funext fun i => by fin_cases i <;> assumption)
end
