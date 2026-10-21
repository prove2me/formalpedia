-- Prove2me | solution 1 for CallNoCall.OneDir.rate_comparison
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:52:37.916042+00:00
-- url     : https://prove2.me/submissions/fe20a513-7285-4e77-8442-ef31edf58a11

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting

set_option autoImplicit false
open CallNoCall.OneDir

namespace AuxRC

lemma int_pow (v R : ℝ) (hv : 0 < v) (hR : 0 < R) (m : ℕ) :
    ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m = R / (v * ((m : ℝ) + 1)) := by
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (R / v),
      HasDerivAt (fun t : ℝ => -(R / (v * ((m : ℝ) + 1))) * ((R - v * t) / R) ^ (m + 1))
        (((R - v * x) / R) ^ m) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (R - v * t) / R) (-v / R) x := by
      have := ((hasDerivAt_id x).const_mul v).const_sub R |>.div_const R
      simpa using this
    have h2 := (h1.pow (m + 1)).const_mul (-(R / (v * ((m : ℝ) + 1))))
    refine h2.congr_deriv ?_
    have hm' : (m:ℝ) + 1 ≠ 0 := hm.ne'
    have hR' : R ≠ 0 := hR.ne'
    have hv' : v ≠ 0 := hv.ne'
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · have : (R - v * (R / v)) / R = 0 := by field_simp; ring
    simp only [this, zero_pow (Nat.succ_ne_zero m), mul_zero, mul_zero, sub_zero]
    simp
    field_simp
    try simp
  · apply Continuous.intervalIntegrable
    fun_prop

lemma int_bounds (v R : ℝ) (hv : 0 < v) (hR : 0 < R) (m : ℕ) (e : ℝ → ℝ) (he : Continuous e)
    (hneg : ∀ t, 0 ≤ t → e t ≤ 0) :
    0 ≤ ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m * Real.exp (e t) ∧
    ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m * Real.exp (e t) ≤ R / (v * ((m : ℝ) + 1)) := by
  have hab : (0:ℝ) ≤ R / v := by positivity
  have hbase : ∀ t ∈ Set.Icc (0:ℝ) (R / v), 0 ≤ (R - v * t) / R := by
    intro t ht
    have : v * t ≤ R := by
      have := ht.2
      rw [le_div_iff₀ hv] at this
      linarith
    apply div_nonneg _ hR.le
    linarith
  refine ⟨?_, ?_⟩
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact mul_nonneg (pow_nonneg (hbase t ht) _) (Real.exp_pos _).le
  · rw [← int_pow v R hv hR m]
    apply intervalIntegral.integral_mono_on hab
    · apply Continuous.intervalIntegrable
      have : Continuous (fun t : ℝ => (R - v * t) / R) := by fun_prop
      exact (this.pow m).mul (Real.continuous_exp.comp he)
    · apply Continuous.intervalIntegrable
      have : Continuous (fun t : ℝ => (R - v * t) / R) := by fun_prop
      exact this.pow m
    · intro t ht
      apply mul_le_of_le_one_right (pow_nonneg (hbase t ht) _)
      exact Real.exp_le_one_iff.2 (hneg t ht.1)

end AuxRC

theorem solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R)
    (hk : 1 ≤ k) (hlam0 : 0 ≤ lam) (n : ℕ) (hn : 1 ≤ n) :
    0 < mu1c d v R k n ∧ mu1c d v R k n ≤ muNC lam d v R k n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hdv : 0 < d / v := by positivity
  by_cases hnk : n ≤ k
  · -- muNC branch 1
    have hI := AuxRC.int_bounds v R hv hR (k - n + 1)
      (fun t => -(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d)) (by fun_prop) (by
        intro t _
        apply div_nonpos_of_nonpos_of_nonneg
        · apply neg_nonpos.2
          have : (0:ℝ) ≤ (n:ℝ) - 1 := by linarith
          positivity
        · positivity)
    have hmuNC : muNC lam d v R k n = (n : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d))) := by
      simp [muNC, hnk]
    rw [hmuNC]
    have hD : 0 < d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d)) := by
      have := hI.1
      linarith
    rcases Nat.lt_or_eq_of_le hnk with hlt | heq
    · have hc : ((k - n + 1 : ℕ) : ℝ) = (k : ℝ) - n + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hnk]; simp
      have hpos : (0:ℝ) < (k : ℝ) - n + 1 := by
        have : (n:ℝ) ≤ k := by exact_mod_cast hnk
        linarith
      have hmu : mu1c d v R k n = (n : ℝ) / (d / v + R / (v * ((k : ℝ) - n + 1))) := by
        simp [mu1c, hlt]
      rw [hmu]
      have h1 : 0 < d / v + R / (v * ((k : ℝ) - n + 1)) := by positivity
      refine ⟨by positivity, ?_⟩
      apply div_le_div_of_nonneg_left (by positivity) hD
      rw [hc] at hI
      have h2 : R / (v * (((k : ℝ) - n + 1) + 1)) ≤ R / (v * ((k : ℝ) - n + 1)) := by
        apply div_le_div_of_nonneg_left hR.le (by positivity)
        nlinarith
      linarith [hI.2]
    · subst heq
      have hmu : mu1c d v R n n = (n : ℝ) / (d / v + R / (2 * v)) := by
        simp [mu1c]
      rw [hmu]
      refine ⟨by positivity, ?_⟩
      apply div_le_div_of_nonneg_left (by positivity) hD
      have e : n - n + 1 = 1 := by omega
      rw [e] at hI hD ⊢
      have h2 : R / (v * (((1:ℕ):ℝ) + 1)) = R / (2 * v) := by
        norm_num; ring_nf
      have := hI.2
      rw [h2] at this
      linarith
  · have hlt : k < n := by omega
    have hI := AuxRC.int_bounds v R hv hR (n - k)
      (fun t => -(lam * v * t ^ 2) / (2 * R)) (by fun_prop) (by
        intro t _
        apply div_nonpos_of_nonpos_of_nonneg
        · apply neg_nonpos.2
          positivity
        · positivity)
    have hmuNC : muNC lam d v R k n = (k : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2) / (2 * R))) := by
      simp [muNC, hnk]
    rw [hmuNC]
    have hD : 0 < d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2) / (2 * R)) := by
      have := hI.1
      linarith
    have hc : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      rw [Nat.cast_sub hlt.le]
    have hmu : mu1c d v R k n = (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1))) := by
      rw [mu1c, if_neg (by omega), if_neg (by omega)]
    have hpos : (0:ℝ) < (n : ℝ) - k + 1 := by
      have : (k:ℝ) ≤ n := by exact_mod_cast hlt.le
      linarith
    rw [hmu]
    refine ⟨by positivity, ?_⟩
    apply div_le_div_of_nonneg_left (by positivity) hD
    rw [hc] at hI
    linarith [hI.2]
