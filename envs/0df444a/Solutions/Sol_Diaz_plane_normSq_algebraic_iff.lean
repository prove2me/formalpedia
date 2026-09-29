-- Prove2me | solution 1 for Diaz.plane_normSq_algebraic_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:03:42.75115+00:00
-- url     : https://prove2.me/submissions/f5aefc43-a3e2-49a6-98dd-95fc0cf5245c

import Mathlib
import Theorems.Thm_Diaz_period_plane_norm
import Theorems.Thm_DiazModulus_pi_sq_transcendental

open ComplexConjugate

private theorem polar2_isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  have h := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q
  rwa [show (algebraMap ℚ ℂ) q = ((q : ℂ)) from rfl] at h

/-- The `c = 0` case of `Diaz.period_plane_norm`. -/
private theorem polar2_normSq_plane (a b : ℝ) (u : ℂ) :
    Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u)
      = (a + b) ^ 2 * Complex.normSq u - 4 * a * b * u.im ^ 2 := by
  have h := Diaz.period_plane_norm u a b 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, zero_sub] at h
  rw [h]; ring

theorem solution {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (a b : ℚ) :
    IsAlgebraic ℚ ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u) : ℝ) : ℂ)
      ↔ a = 0 ∨ b = 0 := by
  have hcastA : ((a : ℂ)) = (((a : ℝ) : ℂ)) := by push_cast; ring
  have hcastB : ((b : ℂ)) = (((b : ℝ) : ℂ)) := by push_cast; ring
  have hkeyR : Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u)
      = ((a : ℝ) + (b : ℝ)) ^ 2 * Complex.normSq u
        - 4 * (a : ℝ) * (b : ℝ) * (k : ℝ) ^ 2 * Real.pi ^ 2 := by
    rw [hcastA, hcastB, polar2_normSq_plane, him]
    ring
  have hkey : ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u) : ℝ) : ℂ)
      = ((((a + b) ^ 2 : ℚ)) : ℂ) * ((Complex.normSq u : ℝ) : ℂ)
        - (((4 * a * b * (k : ℚ) ^ 2 : ℚ)) : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [hkeyR]
    push_cast
    ring
  constructor
  · intro halg
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    apply DiazModulus.pi_sq_transcendental
    set q : ℚ := 4 * a * b * (k : ℚ) ^ 2 with hqdef
    have hq0 : q ≠ 0 := by
      rw [hqdef]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)
        (pow_ne_zero 2 (Int.cast_ne_zero.mpr hk))
    have h1 : IsAlgebraic ℚ (((q : ℚ) : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ)) := by
      have hrw : ((q : ℚ) : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ)
          = ((((a + b) ^ 2 : ℚ)) : ℂ) * ((Complex.normSq u : ℝ) : ℂ)
            - ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u) : ℝ) : ℂ) := by
        rw [hkey, hqdef]
        ring
      rw [hrw]
      exact IsAlgebraic.sub (IsAlgebraic.mul (polar2_isAlgebraic_ratCast _) hn) halg
    have h2 : ((Real.pi ^ 2 : ℝ) : ℂ)
        = ((q⁻¹ : ℚ) : ℂ) * (((q : ℚ) : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ)) := by
      rw [← mul_assoc, ← Rat.cast_mul, inv_mul_cancel₀ hq0, Rat.cast_one, one_mul]
    rw [h2]
    exact IsAlgebraic.mul (polar2_isAlgebraic_ratCast _) h1
  · intro h
    have hz : (((4 * a * b * (k : ℚ) ^ 2 : ℚ)) : ℂ) = 0 := by
      rcases h with h | h <;> subst h <;> push_cast <;> ring
    rw [hkey, hz, zero_mul, sub_zero]
    exact IsAlgebraic.mul (polar2_isAlgebraic_ratCast _) hn
