-- Prove2me | solution 1 for Diaz.period_plane_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:05:38.767649+00:00
-- url     : https://prove2.me/submissions/1b2f4b75-bc75-4fa3-95e9-91d2c66e3cce

import Mathlib
import Theorems.Thm_Diaz_plane_normSq_algebraic_iff

open ComplexConjugate

private theorem polar2_sub_conj_eq (v : ℂ) : v - conj v = ((2 * v.im : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp
  · simp
    ring

theorem solution {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (a b c : ℚ) :
    IsAlgebraic ℚ ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u
        + 2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) : ℝ) : ℂ)
      ↔ (c = -(a * (k : ℚ)) ∨ c = b * (k : ℚ)) := by
  have hkQ : ((k : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hper : (a : ℂ) * u + (b : ℂ) * conj u
      + 2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I
      = (((a + c / (k : ℚ) : ℚ)) : ℂ) * u + (((b - c / (k : ℚ) : ℚ)) : ℂ) * conj u := by
    have hs : u - conj u = ((2 * ((k : ℝ) * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [polar2_sub_conj_eq, him]
    have hexp : (((a + c / (k : ℚ) : ℚ)) : ℂ) * u + (((b - c / (k : ℚ) : ℚ)) : ℂ) * conj u
        = (a : ℂ) * u + (b : ℂ) * conj u
          + (((c / (k : ℚ) : ℚ)) : ℂ) * (u - conj u) := by
      push_cast
      ring
    rw [hexp, hs]
    push_cast
    field_simp
  rw [hper, Diaz.plane_normSq_algebraic_iff hk him hn]
  constructor
  · rintro (h | h)
    · left
      have h2 : c / (k : ℚ) = -a := by linarith
      rw [div_eq_iff hkQ] at h2
      linarith
    · right
      have h2 : c / (k : ℚ) = b := by linarith
      rw [div_eq_iff hkQ] at h2
      linarith
  · rintro (h | h)
    · left
      rw [h]
      field_simp
      ring
    · right
      rw [h]
      field_simp
      ring
