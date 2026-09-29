-- Prove2me | solution 1 for DS3Micro.entropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:22:55.626914+00:00
-- url     : https://prove2.me/submissions/6401b77f-707f-4e71-befd-8965e786ff4f

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro

/-- The elementary real integral after the substitution `E = 2 cosh t`. -/
theorem aux_dsent_int (β : ℝ) (hβ : 0 < β) :
    ∫ E in (2 : ℝ)..(2 * Real.cosh (Real.pi / β)), Real.sin (β * Real.arcosh (E / 2)) =
      2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2) := by
  set T : ℝ := Real.pi / β with hT
  have hT0 : 0 < T := div_pos Real.pi_pos hβ
  have hg : ContinuousOn (fun E : ℝ => Real.sin (β * Real.arcosh (E / 2)))
      ((fun t : ℝ => 2 * Real.cosh t) '' Set.uIcc 0 T) := by
    have hc : ContinuousOn (fun E : ℝ => Real.sin (β * Real.arcosh (E / 2))) (Set.Ici 2) := by
      apply Real.continuous_sin.comp_continuousOn
      apply ContinuousOn.mul continuousOn_const
      apply Real.continuousOn_arcosh.comp (continuousOn_id.div_const 2)
      intro x hx
      simp only [Set.mem_Ici] at hx ⊢
      simp only [id]
      linarith
    apply hc.mono
    rintro _ ⟨t, _, rfl⟩
    simp only [Set.mem_Ici]
    have := Real.one_le_cosh t
    linarith
  have h1 := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := T)
    (f := fun t : ℝ => 2 * Real.cosh t) (f' := fun t : ℝ => 2 * Real.sinh t)
    (fun x _ => by simpa using (Real.hasDerivAt_cosh x).const_mul 2)
    (by fun_prop) hg
  simp only [Real.cosh_zero, mul_one] at h1
  rw [← h1]
  have h2 : ∫ t in (0 : ℝ)..T,
      ((fun E : ℝ => Real.sin (β * Real.arcosh (E / 2))) ∘ fun t : ℝ => 2 * Real.cosh t) t *
        (2 * Real.sinh t) =
      ∫ t in (0 : ℝ)..T, Real.sin (β * t) * (2 * Real.sinh t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT0.le] at ht
    simp only [Function.comp]
    congr 3
    rw [mul_div_cancel_left₀ _ (two_ne_zero)]
    exact Real.arcosh_cosh ht.1
  rw [h2]
  have hβ2 : (1 + β ^ 2) ≠ 0 := by positivity
  have hderiv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt
      (fun t : ℝ => 2 * (Real.cosh t * Real.sin (β * t) - β * (Real.sinh t * Real.cos (β * t))) /
        (1 + β ^ 2))
      (Real.sin (β * t) * (2 * Real.sinh t)) t := by
    intro t _
    have hs : HasDerivAt (fun t : ℝ => Real.sin (β * t)) (Real.cos (β * t) * (β * 1)) t :=
      (Real.hasDerivAt_sin (β * t)).comp t ((hasDerivAt_id t).const_mul β)
    have hc : HasDerivAt (fun t : ℝ => Real.cos (β * t)) (-Real.sin (β * t) * (β * 1)) t :=
      (Real.hasDerivAt_cos (β * t)).comp t ((hasDerivAt_id t).const_mul β)
    have := ((((Real.hasDerivAt_cosh t).mul hs).sub
      (((Real.hasDerivAt_sinh t).mul hc).const_mul β)).const_mul 2).div_const (1 + β ^ 2)
    refine HasDerivAt.congr_deriv this ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable
    fun_prop)]
  have hβT : β * T = Real.pi := by
    rw [hT, mul_div_assoc']; exact mul_div_cancel_left₀ _ hβ.ne'
  simp only [hβT, Real.sin_pi, Real.cos_pi, mul_zero, Real.sin_zero, Real.cos_zero,
    Real.sinh_zero, Real.cosh_zero]
  field_simp
  ring

end DS3Micro

open DS3Micro

theorem solution (b : ℂ) (hb : InRegime b) (S0 : ℝ) :
    SdSMicro b S0 = 2 * (S0 : ℂ) + 2 * Complex.log
        (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
            Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
          ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) ∧
      SdSMicro b S0 = 2 * Complex.log (tension b S0 / (2 * (Real.pi : ℂ) * Complex.I)) := by
  obtain ⟨β, hβ, hb2⟩ := hb
  have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hinv : (b ^ 2)⁻¹ = -Complex.I * ((β : ℂ)⁻¹) := by
    rw [hb2, mul_inv, Complex.inv_I]
  -- closed forms of the sines
  have hs1 : Complex.sin ((Real.pi : ℂ) * b ^ 2) = (Real.sinh (Real.pi * β) : ℂ) * Complex.I := by
    rw [hb2, Complex.ofReal_sinh, ← Complex.sin_mul_I]
    congr 1
    push_cast
    ring
  have hs2 : Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) =
      -((Real.sinh (Real.pi / β) : ℂ) * Complex.I) := by
    rw [hinv, Complex.ofReal_sinh, ← Complex.sin_mul_I, ← Complex.sin_neg]
    congr 1
    push_cast
    ring
  have hE0 : (E0 b).re = 2 * Real.cosh (Real.pi / β) := by
    have : E0 b = ((2 * Real.cosh (Real.pi / β) : ℝ) : ℂ) := by
      rw [E0, hinv]
      push_cast
      rw [← Complex.cos_mul_I, ← Complex.cos_neg]
      congr 2
      ring
    rw [this, Complex.ofReal_re]
  -- the integrand is real
  set K : ℝ := Real.exp S0 * (2 / Real.pi) * Real.sinh (Real.pi * β) with hK
  have hint : ∀ E : ℝ, (Real.exp S0 : ℂ) * rho0 b E =
      ((K * Real.sin (β * Real.arcosh (E / 2)) : ℝ) : ℂ) := by
    intro E
    rw [rho0, hb2, hK]
    push_cast
    have e1 : -Complex.I * (Real.pi : ℂ) * (Complex.I * (β : ℂ)) = (Real.pi : ℂ) * β := by
      ring_nf
      rw [Complex.I_sq]
      ring
    have e2 : -Complex.I * (Complex.I * (β : ℂ)) * (Real.arcosh (E / 2) : ℂ) =
        (β : ℂ) * (Real.arcosh (E / 2) : ℂ) := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e1, e2]
    ring
  -- closed form of Neff
  set X : ℝ := 4 * β * Real.sinh (Real.pi * β) * Real.sinh (Real.pi / β) /
    (Real.pi * (1 + β ^ 2)) with hX
  have hNeff : Neff b S0 = ((Real.exp S0 * X : ℝ) : ℂ) := by
    rw [Neff, hE0]
    simp_rw [hint]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
      aux_dsent_int β hβ]
    congr 1
    rw [hK, hX]
    field_simp
    ring
  have hXpos : 0 < X := by
    rw [hX]
    have := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hβ)
    have := Real.sinh_pos_iff.mpr (div_pos Real.pi_pos hβ)
    have := Real.pi_pos
    positivity
  have hlog : Complex.log ((Real.exp S0 * X : ℝ) : ℂ) = (S0 : ℂ) + Complex.log (X : ℂ) := by
    rw [← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hXpos.le,
      Real.log_mul (Real.exp_pos S0).ne' hXpos.ne', Real.log_exp]
    push_cast
    ring
  have hβ2 : (1 + (β : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + β ^ 2 := by positivity
    exact_mod_cast this.ne'
  refine ⟨?_, ?_⟩
  · rw [SdSMicro, hNeff, hlog]
    have hXc : (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
            Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
          ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) = (X : ℂ) := by
      rw [hs1, hs2, hinv, hb2, hX]
      push_cast
      have hden : (Real.pi : ℂ) * (-Complex.I * (β : ℂ)⁻¹ - Complex.I * (β : ℂ)) ≠ 0 := by
        have : -Complex.I * (β : ℂ)⁻¹ - Complex.I * (β : ℂ) =
            -Complex.I * (1 + (β : ℂ) ^ 2) / β := by
          field_simp
          ring
        rw [this]
        apply mul_ne_zero hpi0
        apply div_ne_zero _ hβ0
        exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hβ2
      rw [div_eq_div_iff hden (mul_ne_zero hpi0 hβ2)]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hXc]
    ring
  · rw [SdSMicro]
    congr 2
    rw [hNeff, tension, tensionHat, show b ^ 4 = (b ^ 2) ^ 2 by ring, hs1, hs2, hb2, hX]
    push_cast
    have h4 : (1 - (Complex.I * (β : ℂ)) ^ 2) = 1 + (β : ℂ) ^ 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h4]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
