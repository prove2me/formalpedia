-- Prove2me | solution 1 for FastFourierTransform.idft_dft
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:31:06.24617+00:00
-- url     : https://prove2.me/submissions/f3dc072b-7929-4c5a-9e9a-86b4c8a17a3f

import Mathlib
import Definitions.Def_FastFourierTransform_dft
import Definitions.Def_FastFourierTransform_idft

open FastFourierTransform

namespace Ag3Aux_IdftDft

theorem geo (n : ℕ) (hn : 0 < n) (m j : ℕ) (hm : m < n) (hj : j < n) :
    ∑ k ∈ Finset.range n,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ)))
      = if j = m then (n : ℂ) else 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (j : ℂ)) / (n : ℂ)) with hζ
  have hterm : ∀ k : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ))) = ζ ^ k := by
    intro k
    rw [← Complex.exp_add, hζ, ← Complex.exp_nat_mul]
    congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · subst h
    simp [hζ]
  · have hζ1 : ζ ≠ 1 := by
      rw [hζ, Ne, Complex.exp_eq_one_iff]
      rintro ⟨q, hq⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : ((m : ℂ) - (j : ℂ)) = (q : ℂ) * n := by
        field_simp at hq; linear_combination hq
      have h3 : ((m : ℤ) - (j : ℤ)) = q * n := by exact_mod_cast h2
      rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
      · have : q * (n : ℤ) ≤ -n := by nlinarith
        omega
      · subst hq0; omega
      · have : q * (n : ℤ) ≥ n := by nlinarith
        omega
    have hζn : ζ ^ n = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      rw [show (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (j : ℂ)) / (n : ℂ))
          = (((m : ℤ) - (j : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div]

end Ag3Aux_IdftDft

open Ag3Aux_IdftDft

theorem solution (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) (m : ℕ) (hm : m < n) :
    idft n (dft n x) m = x m := by
  unfold idft dft
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      x j * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (k : ℂ) / (n : ℂ))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ))
      = x j * (if j = m then (n : ℂ) else 0) := by
    intro j hj
    rw [← geo n hn m j hm (Finset.mem_range.mp hj), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl this]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' , if_pos (Finset.mem_range.mpr hm)]
  field_simp
