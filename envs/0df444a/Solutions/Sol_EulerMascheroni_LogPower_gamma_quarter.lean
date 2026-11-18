-- Prove2me | solution 1 for EulerMascheroni.LogPower.gamma_quarter
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:45:49.914976+00:00
-- url     : https://prove2.me/submissions/f78962a4-fb33-43e8-b426-96e1042e48b3

import Mathlib

open MeasureTheory Set Real

lemma abs_log_le (t : ℝ) (ht : 0 < t) : |Real.log t| ≤ t + 2 * t ^ (-(1/2:ℝ)) := by
  have hp : 0 < t ^ (-(1/2:ℝ)) := Real.rpow_pos_of_pos ht _
  rcases le_or_gt 1 t with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos ht
    linarith
  · rw [abs_of_neg (Real.log_neg ht h)]
    have h1 := Real.log_le_sub_one_of_pos hp
    rw [Real.log_rpow ht] at h1
    linarith

lemma int_pow (m : ℕ) : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ m) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := (m:ℝ) + 1) (by positivity)
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]

lemma int_logpow (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m * (Real.log t * Real.exp (-t))) (Ioi 0) := by
  have hA := Real.GammaIntegral_convergent (s := (m:ℝ) + 2) (by positivity)
  have hB := Real.GammaIntegral_convergent (s := (m:ℝ) + 1/2) (by positivity)
  refine Integrable.mono' (hA.add (hB.const_mul 2)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have : t ≠ 0 := (mem_Ioi.mp ht).ne'
    fun_prop (disch := assumption)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    have he : 0 < Real.exp (-t) := Real.exp_pos _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos he, abs_of_nonneg (by positivity)]
    have hl := abs_log_le t ht
    have e1 : t ^ ((m:ℝ) + 2 - 1) = t ^ m * t := by
      rw [show (m:ℝ) + 2 - 1 = (m:ℝ) + 1 by ring, Real.rpow_add ht, Real.rpow_natCast,
        Real.rpow_one]
    have e2 : t ^ ((m:ℝ) + 1/2 - 1) = t ^ m * t ^ (-(1/2:ℝ)) := by
      rw [show (m:ℝ) + 1/2 - 1 = (m:ℝ) + (-(1/2)) by ring, Real.rpow_add ht, Real.rpow_natCast]
    simp only [Pi.add_apply]
    rw [e1, e2]
    have hm : 0 ≤ t ^ m := by positivity
    calc t ^ m * (|Real.log t| * Real.exp (-t))
        ≤ t ^ m * ((t + 2 * t ^ (-(1/2:ℝ))) * Real.exp (-t)) := by gcongr
      _ = _ := by ring

lemma key_moment (m : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ m * (Real.log t * Real.exp (-t)) =
      (m.factorial : ℝ) * (-Real.eulerMascheroniConstant + harmonic m) := by
  have hs : 0 < ((m : ℂ) + 1).re := by simp; positivity
  have h1 := Complex.hasDerivAt_GammaIntegral hs
  have hopen : IsOpen {s : ℂ | 0 < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have h2 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t:ℂ) ^ (((m:ℂ) + 1) - 1) * (Real.log t * Real.exp (-t))) ((m:ℂ) + 1) := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hs] with a ha using Complex.Gamma_eq_integral ha
  have h2' : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t:ℂ) ^ (((m:ℂ) + 1) - 1) * (Real.log t * Real.exp (-t)))
      (((m:ℝ) + 1 : ℝ) : ℂ) := by
    convert h2 using 1; push_cast; rfl
  have h3 := h2'.real_of_complex
  have h4 : (fun x : ℝ => (Complex.Gamma (x:ℂ)).re) = Real.Gamma := by
    funext x; rw [Complex.Gamma_ofReal]; simp
  rw [h4] at h3
  have huniq := h3.unique (Real.hasDerivAt_Gamma_nat m)
  rw [← huniq]
  have hint : (∫ t : ℝ in Ioi 0, (t:ℂ) ^ (((m:ℂ) + 1) - 1) * (Real.log t * Real.exp (-t))) =
      ((∫ t in Ioi (0:ℝ), t ^ m * (Real.log t * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [add_sub_cancel_right]
    rw [Complex.cpow_natCast]
    push_cast; ring
  rw [hint]; simp

theorem laplace_log_moment (m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (-s * u) * u ^ m * Real.log u
      = (Nat.factorial m : ℝ) * ((harmonic m : ℝ) - Real.eulerMascheroniConstant - Real.log s) / s ^ (m + 1) := by
  set G : ℝ → ℝ := fun t => (s ^ m)⁻¹ * (t ^ m * (Real.log t * Real.exp (-t))) -
    (s ^ m)⁻¹ * Real.log s * (Real.exp (-t) * t ^ m) with hG
  have hcongr : ∫ u in Ioi (0:ℝ), Real.exp (-s * u) * u ^ m * Real.log u =
      ∫ u in Ioi (0:ℝ), G (s * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu : 0 < u := hu
    simp only [hG]
    rw [Real.log_mul hs.ne' hu.ne', mul_pow]
    field_simp
    ring_nf
  rw [hcongr, integral_comp_mul_left_Ioi G 0 hs, mul_zero, smul_eq_mul, hG,
    integral_sub ((int_logpow m).const_mul _) ((int_pow m).const_mul _),
    integral_const_mul, integral_const_mul, key_moment]
  have hg : ∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ m = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_eq_integral (by positivity)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [hg]
  field_simp
  ring

theorem solution :
    ∫ u in Set.Ioi (0:ℝ), (Real.exp (-2 * u) - Real.exp (-4 * u)) * (-Real.log u)
      = Real.eulerMascheroniConstant / 4 := by
  have hγ : 0 < Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have h2 := laplace_log_moment 0 2 two_pos
  have h4 := laplace_log_moment 0 4 (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [harmonic_zero, Rat.cast_zero, Nat.factorial_zero, Nat.cast_one, pow_zero,
    mul_one, zero_add, pow_one] at h2 h4
  have i2 : IntegrableOn (fun u : ℝ => Real.exp (-2 * u) * Real.log u) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero; rw [h2]
    have : 0 < Real.eulerMascheroniConstant + Real.log 2 := by linarith
    intro h; field_simp at h; linarith
  have i4 : IntegrableOn (fun u : ℝ => Real.exp (-4 * u) * Real.log u) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero; rw [h4]
    intro h; field_simp at h; linarith
  have hc : ∫ u in Set.Ioi (0:ℝ), (Real.exp (-2 * u) - Real.exp (-4 * u)) * (-Real.log u) =
      ∫ u in Set.Ioi (0:ℝ), (Real.exp (-4 * u) * Real.log u - Real.exp (-2 * u) * Real.log u) := by
    congr 1; funext u; ring
  rw [hc, integral_sub i4 i2, h2, h4, hl4]
  ring
