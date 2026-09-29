-- Prove2me | solution 1 for Diaz.q_translate_unique
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:10:46.254075+00:00
-- url     : https://prove2.me/submissions/e77f481c-0776-4e9a-8511-ea632d2251f4

import Mathlib

open ComplexConjugate

theorem solution {K : Subfield ℂ} {u : ℂ}
    (hρ : u * conj u ∈ K) (hπ : ((Real.pi : ℂ)) ^ 2 ∉ K)
    {r r' : ℚ} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : (u + 2 * (Real.pi : ℂ) * (r : ℂ) * Complex.I)
          * conj (u + 2 * (Real.pi : ℂ) * (r : ℂ) * Complex.I) ∈ K)
    (h' : (u + 2 * (Real.pi : ℂ) * (r' : ℂ) * Complex.I)
          * conj (u + 2 * (Real.pi : ℂ) * (r' : ℂ) * Complex.I) ∈ K) :
    r = r' := by
  set Z : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (conj u - u) with hZdef
  have e : ∀ s : ℚ, (u + 2 * (Real.pi : ℂ) * (s : ℂ) * Complex.I)
      * conj (u + 2 * (Real.pi : ℂ) * (s : ℂ) * Complex.I)
      = u * conj u + (s : ℂ) * (Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)) := by
    intro s
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_ratCast, hZdef]
    linear_combination (-4 * (Real.pi : ℂ) ^ 2 * (s : ℂ) ^ 2) * hI
  rw [e r] at h
  rw [e r'] at h'
  have step : ∀ s : ℚ, s ≠ 0 →
      (s : ℂ) * (Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)) + u * conj u ∈ K →
      Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ) ∈ K := by
    intro s hs hm
    have hm2 : (s : ℂ) * (Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)) ∈ K := by
      have := sub_mem hm hρ
      simpa using this
    have hinv : ((s⁻¹ : ℚ) : ℂ) ∈ K := SubfieldClass.ratCast_mem K _
    have hmul := mul_mem hinv hm2
    have hs' : ((s : ℂ)) ≠ 0 := by exact_mod_cast hs
    rwa [show ((s⁻¹ : ℚ) : ℂ) * ((s : ℂ) * (Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)))
        = Z + 4 * (Real.pi : ℂ) ^ 2 * (s : ℂ) by push_cast; field_simp] at hmul
  have k1 : Z + 4 * (Real.pi : ℂ) ^ 2 * (r : ℂ) ∈ K := step r hr (by rw [add_comm] at h; exact h)
  have k2 : Z + 4 * (Real.pi : ℂ) ^ 2 * (r' : ℂ) ∈ K :=
    step r' hr' (by rw [add_comm] at h'; exact h')
  by_contra hne
  have hd : ((r : ℂ)) - ((r' : ℂ)) ≠ 0 := by
    simp only [sub_ne_zero]
    exact_mod_cast hne
  have hdiff : 4 * (Real.pi : ℂ) ^ 2 * ((r : ℂ) - (r' : ℂ)) ∈ K := by
    have := sub_mem k1 k2
    convert this using 1
    ring
  have hc : (((4 * (r - r'))⁻¹ : ℚ) : ℂ) ∈ K := SubfieldClass.ratCast_mem K _
  apply hπ
  have hfin := mul_mem hc hdiff
  rwa [show (((4 * (r - r'))⁻¹ : ℚ) : ℂ) * (4 * (Real.pi : ℂ) ^ 2 * ((r : ℂ) - (r' : ℂ)))
      = ((Real.pi : ℂ)) ^ 2 by push_cast; field_simp] at hfin
