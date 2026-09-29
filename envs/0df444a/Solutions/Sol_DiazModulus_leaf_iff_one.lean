-- Prove2me | solution 1 for DiazModulus.leaf_iff_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:01:36.653551+00:00
-- url     : https://prove2.me/submissions/4bda2623-3b9a-49a3-b94b-558c471d7e26

import Definitions.Def_DiazModulus
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic

open Complex ComplexConjugate

private theorem polar2_isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  have h := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q
  rwa [show (algebraMap ℚ ℂ) q = ((q : ℂ)) from rfl] at h

private theorem polar2_exp_eq_of_im {z : ℂ} {k : ℤ} (hk : z.im = (k : ℝ) * Real.pi) :
    Complex.exp z = ((Real.exp z.re * Real.cos ((k : ℝ) * Real.pi) : ℝ) : ℂ) := by
  have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := Real.sin_eq_zero_iff.mpr ⟨k, rfl⟩
  apply Complex.ext
  · simp only [Complex.exp_re, Complex.ofReal_re, hk]
  · simp only [Complex.exp_im, Complex.ofReal_im, hk, hsin, mul_zero]

private theorem polar2_cos_int_mul_pi_mul_self (k : ℤ) :
    Real.cos ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi) = 1 := by
  have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := Real.sin_eq_zero_iff.mpr ⟨k, rfl⟩
  have h := Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi)
  rw [hsin] at h
  nlinarith [h]

private theorem polar2_isAlgebraic_mul_cos_iff (k : ℤ) (x : ℝ) :
    IsAlgebraic ℚ ((x * Real.cos ((k : ℝ) * Real.pi) : ℝ) : ℂ) ↔ IsAlgebraic ℚ ((x : ℝ) : ℂ) := by
  rcases mul_self_eq_one_iff.mp (polar2_cos_int_mul_pi_mul_self k) with h | h <;>
    rw [h] <;> push_cast <;> simp
  constructor
  · intro hx
    simpa using hx.neg
  · intro hx
    simpa using hx.neg

private theorem polar2_norm_sq_eq (u : ℂ) :
    (((‖u‖ : ℝ) : ℂ)) ^ 2 = ((u.re ^ 2 + u.im ^ 2 : ℝ) : ℂ) := by
  have : (‖u‖ : ℝ) ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  push_cast [← this]
  ring

private theorem polar2_natAbs_cast_sq (k : ℤ) : ((k.natAbs : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem solution :
    (∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
        u.im ≠ 0 → Complex.exp u ≠ 1 → u.re ≠ 0 → Transcendental ℚ (Complex.exp u))
      ↔ (∀ t : ℝ, t ≠ 0 → IsAlgebraic ℚ ((Real.exp t : ℝ) : ℂ) →
          Transcendental ℚ ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ)) := by
  constructor
  · intro h t ht hexpt halg
    set u : ℂ := ⟨t, (1 : ℝ) * Real.pi⟩ with hu_def
    have hu_re : u.re = t := rfl
    have hu_im : u.im = ((1 : ℤ) : ℝ) * Real.pi := by rw [hu_def]; norm_num
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hu0 : u ≠ 0 := by
      intro h0
      exact ht (by simpa [hu_re] using congrArg Complex.re h0)
    have hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) := by
      refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
      rw [polar2_norm_sq_eq u, hu_re, hu_im]
      have hrw : (t ^ 2 + (((1 : ℤ) : ℝ) * Real.pi) ^ 2 : ℝ) = t ^ 2 + Real.pi ^ 2 := by
        push_cast; ring
      rw [hrw]
      exact halg
    have hz := polar2_exp_eq_of_im (z := u) (k := 1) hu_im
    have himzero : (Complex.exp u).im = 0 := by rw [hz]; exact Complex.ofReal_im _
    have hne1 : Complex.exp u ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have : u.re = 0 := by rw [hn]; simp
      exact ht (by rwa [hu_re] at this)
    have hexpu : IsAlgebraic ℚ (Complex.exp u) := by
      rw [hz, hu_re]
      exact (polar2_isAlgebraic_mul_cos_iff 1 (Real.exp t)).mpr hexpt
    refine h u hu0 hmod himzero ?_ hne1 (by rw [hu_re]; exact ht) hexpu
    rw [hu_im]
    simpa using hpi
  · intro h u hu hmod hre him _hne hurne hexp
    have hsin : Real.sin u.im = 0 := by
      have : Real.exp u.re * Real.sin u.im = 0 := by
        simpa [Complex.exp_im] using hre
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (Real.exp_ne_zero _)
      · exact h0
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact him (by simpa using hk.symm)
    have hexpre : IsAlgebraic ℚ ((Real.exp u.re : ℝ) : ℂ) := by
      have hz := polar2_exp_eq_of_im (z := u) (k := k) hk.symm
      rw [hz] at hexp
      exact (polar2_isAlgebraic_mul_cos_iff k (Real.exp u.re)).mp hexp
    have hmod2 : IsAlgebraic ℚ ((u.re ^ 2 + (k : ℝ) ^ 2 * Real.pi ^ 2 : ℝ) : ℂ) := by
      have hp := hmod.pow (n := 2)
      rw [polar2_norm_sq_eq u] at hp
      have himsq : u.im ^ 2 = (k : ℝ) ^ 2 * Real.pi ^ 2 := by rw [← hk]; ring
      rwa [himsq] at hp
    set t : ℝ := u.re with ht_def
    set N : ℕ := k.natAbs with hN
    have hN0 : 0 < N := Int.natAbs_pos.mpr hk0
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    have hkQ : (k : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    have hNk : ((N : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by rw [hN]; exact polar2_natAbs_cast_sq k
    set s : ℝ := t / (N : ℝ) with hs
    have hs0 : s ≠ 0 := div_ne_zero hurne (ne_of_gt hNR)
    have hsexp : IsAlgebraic ℚ ((Real.exp s : ℝ) : ℂ) := by
      have hbase : IsAlgebraic ℚ (Complex.exp ((t : ℝ) : ℂ)) := by
        rw [Complex.ofReal_exp] at hexpre
        exact hexpre
      have hmul := Diaz.exp_ratMul_isAlgebraic hbase ((1 : ℚ) / (N : ℚ))
      have hrw : ((((1 : ℚ) / (N : ℚ) : ℚ) : ℂ)) * ((t : ℝ) : ℂ) = ((s : ℝ) : ℂ) := by
        rw [hs, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul]
        norm_num
        ring
      rw [hrw, ← Complex.ofReal_exp] at hmul
      exact hmul
    have hssq : s ^ 2 = t ^ 2 / (k : ℝ) ^ 2 := by
      rw [hs, div_pow, hNk]
    have hcoef : ((s ^ 2 + Real.pi ^ 2 : ℝ) : ℂ)
        = (((1 / (k : ℚ) ^ 2 : ℚ) : ℂ)) * ((t ^ 2 + (k : ℝ) ^ 2 * Real.pi ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_ratCast, ← Complex.ofReal_mul]
      congr 1
      rw [hssq]
      push_cast
      field_simp
    have hrat : IsAlgebraic ℚ (((1 / (k : ℚ) ^ 2 : ℚ) : ℂ)) := polar2_isAlgebraic_ratCast _
    have hfinal : IsAlgebraic ℚ ((s ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) := by
      rw [hcoef]; exact hrat.mul hmod2
    exact h s hs0 hsexp hfinal
