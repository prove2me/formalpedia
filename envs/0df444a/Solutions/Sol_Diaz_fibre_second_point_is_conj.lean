-- Prove2me | solution 1 for Diaz.fibre_second_point_is_conj
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:07:33.774655+00:00
-- url     : https://prove2.me/submissions/287dc84f-b9c5-407e-ac1b-304f87047458

import Mathlib
import Theorems.Thm_Diaz_period_plane_classification

open ComplexConjugate

private theorem polar2_ratMul_im (q : ℚ) (u : ℂ) : ((q : ℂ) * u).im = (q : ℝ) * u.im := by
  simp [Complex.mul_im]

private theorem polar2_sub_conj_eq (v : ℂ) : v - conj v = ((2 * v.im : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp
  · simp
    ring

theorem solution {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (q : ℚ) (n : ℤ) (hn0 : n ≠ 0)
    (halg : IsAlgebraic ℚ ((Complex.normSq ((q : ℂ) * u
        + 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) : ℝ) : ℂ)) :
    q * (k : ℚ) = -(n : ℚ)
      ∧ (q : ℂ) * u + 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I = conj ((q : ℂ) * u)
      ∧ (Complex.exp ((q : ℂ) * u)).im = 0 := by
  have hcastn : ((n : ℂ)) = (((n : ℚ) : ℂ)) := by push_cast; ring
  have hcl := (Diaz.period_plane_classification hk him hn q 0 (n : ℚ)).mp (by
    rw [hcastn] at halg
    simpa using halg)
  have hqk : q * (k : ℚ) = -(n : ℚ) := by
    rcases hcl with h | h
    · linarith
    · simp at h
      exact absurd (by exact_mod_cast h : (n : ℤ) = 0) hn0
  refine ⟨hqk, ?_, ?_⟩
  · have hs : u - conj u = ((2 * ((k : ℝ) * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [polar2_sub_conj_eq, him]
    have hnk : ((n : ℂ)) = -((q : ℂ) * ((k : ℤ) : ℂ)) := by
      have h := congrArg (fun x : ℚ => ((x : ℂ))) hqk
      simp only [Rat.cast_mul, Rat.cast_neg] at h
      push_cast at h ⊢
      linear_combination h
    rw [hnk]
    have hconj : conj ((q : ℂ) * u) = (q : ℂ) * conj u := by
      simp
    rw [hconj]
    have hd : (q : ℂ) * u - (q : ℂ) * conj u
        = (q : ℂ) * (((2 * ((k : ℝ) * Real.pi) : ℝ) : ℂ) * Complex.I) := by
      rw [← mul_sub, hs]
    push_cast at hd ⊢
    linear_combination hd
  · have him2 : ((q : ℂ) * u).im = -((n : ℝ) * Real.pi) := by
      rw [polar2_ratMul_im, him]
      have : (q : ℝ) * (k : ℝ) = -(n : ℝ) := by exact_mod_cast hqk
      rw [← mul_assoc, this]
      ring
    rw [Complex.exp_im, him2]
    have : Real.sin (-((n : ℝ) * Real.pi)) = 0 := by
      rw [Real.sin_neg, Real.sin_int_mul_pi]
      ring
    rw [this, mul_zero]
