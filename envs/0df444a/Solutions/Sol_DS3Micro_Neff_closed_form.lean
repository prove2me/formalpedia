-- Prove2me | solution 1 for DS3Micro.Neff_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:08:12.724673+00:00
-- url     : https://prove2.me/submissions/67cf5e23-9d22-404c-b850-c53c4737f604

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro

/-- The real integral after the substitution `E = 2 cosh u`. -/
theorem aux_neff_sinh_int (β : ℝ) (hβ : 0 < β) :
    ∫ u in (0 : ℝ)..Real.pi / β, 2 * (Real.sin (β * u) * Real.sinh u) =
      2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2) := by
  have hpos : (0 : ℝ) < 1 + β ^ 2 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / β),
      HasDerivAt (fun u : ℝ => 2 * (Real.sin (β * u) * Real.cosh u -
          β * Real.cos (β * u) * Real.sinh u) / (1 + β ^ 2))
        (2 * (Real.sin (β * x) * Real.sinh x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => β * u) β x := by
      simpa using (hasDerivAt_id x).const_mul β
    have hs := (Real.hasDerivAt_sin (β * x)).comp x h1
    have hc := (Real.hasDerivAt_cos (β * x)).comp x h1
    have hch := Real.hasDerivAt_cosh x
    have hsh := Real.hasDerivAt_sinh x
    have := ((((hs.mul hch).sub ((hc.const_mul β).mul hsh)).const_mul 2).div_const (1 + β ^ 2))
    refine this.congr_deriv ?_
    simp only [Function.comp]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hβne : β ≠ 0 := hβ.ne'
  have : β * (Real.pi / β) = Real.pi := by field_simp
  simp only [this, Real.sin_pi, Real.cos_pi, mul_zero, Real.sin_zero, Real.sinh_zero,
    Real.cosh_zero, Real.cos_zero]
  field_simp
  ring

/-- The real integral `∫_2^{2 cosh(π/β)} sin(β arcosh(E/2)) dE`. -/
theorem aux_neff_real_int (β : ℝ) (hβ : 0 < β) :
    ∫ E in (2 : ℝ)..2 * Real.cosh (Real.pi / β), Real.sin (β * Real.arcosh (E / 2)) =
      2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := Real.pi / β)
    (f := fun x : ℝ => 2 * Real.cosh x) (f' := fun x : ℝ => 2 * Real.sinh x)
    (g := fun E : ℝ => Real.sin (β * Real.arcosh (E / 2)))
    (by apply Continuous.continuousOn; fun_prop)
    (by
      intro x _
      simpa using (Real.hasDerivAt_cosh x).const_mul 2)
    (by
      intro x hx
      have hπβ : 0 ≤ Real.pi / β := by positivity
      rw [min_eq_left hπβ] at hx
      have := Real.sinh_pos_iff.mpr hx.1
      positivity)
  simp only [Real.cosh_zero, mul_one] at hsub
  rw [← hsub, ← aux_neff_sinh_int β hβ]
  apply intervalIntegral.integral_congr
  intro x hx
  have hπβ : 0 ≤ Real.pi / β := by positivity
  rw [Set.uIcc_of_le hπβ] at hx
  simp only [Function.comp]
  rw [show 2 * Real.cosh x / 2 = Real.cosh x by ring, Real.arcosh_cosh hx.1]
  ring

end DS3Micro

open DS3Micro

theorem solution (b : ℂ) (hb : InRegime b) (S0 : ℝ) :
    Neff b S0 = (Real.exp S0 : ℂ) *
      (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
          Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
        ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) := by
  obtain ⟨β, hβ, hb2⟩ := hb
  have hβne : β ≠ 0 := hβ.ne'
  have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβne
  have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hinv : (Complex.I * (β : ℂ))⁻¹ = -Complex.I * ((β : ℂ))⁻¹ := by
    rw [mul_inv, Complex.inv_I]
  have hE0 : (E0 b).re = 2 * Real.cosh (Real.pi / β) := by
    unfold E0
    rw [hb2, hinv]
    have : (Real.pi : ℂ) * (-Complex.I * (β : ℂ)⁻¹) = -(((Real.pi / β : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.cos_neg, Complex.cos_mul_I, ← Complex.ofReal_cosh,
      show (2 : ℂ) * ((Real.cosh (Real.pi / β) : ℝ) : ℂ) =
        ((2 * Real.cosh (Real.pi / β) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hint : ∀ E : ℝ, (Real.exp S0 : ℂ) * rho0 b E =
      ((Real.exp S0 * (2 / Real.pi * Real.sinh (Real.pi * β)) *
        Real.sin (β * Real.arcosh (E / 2)) : ℝ) : ℂ) := by
    intro E
    unfold rho0
    rw [hb2]
    have h1 : -Complex.I * (Real.pi : ℂ) * (Complex.I * (β : ℂ)) = ((Real.pi * β : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have h2 : -Complex.I * (Complex.I * (β : ℂ)) * (Real.arcosh (E / 2) : ℂ) =
        ((β * Real.arcosh (E / 2) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [h1, h2, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
    push_cast
    ring
  unfold Neff
  rw [hE0]
  simp_rw [hint]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    aux_neff_real_int β hβ, hb2, hinv]
  have hs1 : Complex.sin ((Real.pi : ℂ) * (Complex.I * (β : ℂ))) =
      Complex.sinh ((Real.pi * β : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.sin_mul_I]; push_cast; ring_nf
  have hs2 : Complex.sin ((Real.pi : ℂ) * (-Complex.I * (β : ℂ)⁻¹)) =
      -(Complex.sinh ((Real.pi / β : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.sin_mul_I, ← Complex.sin_neg]; push_cast; ring_nf
  rw [hs1, hs2, ← Complex.ofReal_sinh, ← Complex.ofReal_sinh]
  have hD : (Real.pi : ℂ) * (-Complex.I * (β : ℂ)⁻¹ - Complex.I * (β : ℂ)) =
      -Complex.I * (Real.pi : ℂ) * ((1 + (β : ℂ) ^ 2) / β) := by
    field_simp; ring
  have h1b : ((1 : ℂ) + (β : ℂ) ^ 2) ≠ 0 := by
    have : (1 : ℝ) + β ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [hD]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf
