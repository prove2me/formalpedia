-- Prove2me | solution 1 for DS3Micro.entropy_matches_sphere
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:47.166168+00:00
-- url     : https://prove2.me/submissions/5b044d66-5e70-4757-bef4-eb91a6da836f

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro

lemma aux_ds3e_G_deriv (β t : ℝ) (hβ : 0 < β) :
    HasDerivAt (fun t : ℝ => 2 * (Real.cosh t * Real.sin (β * t) -
        β * Real.sinh t * Real.cos (β * t)) / (1 + β ^ 2))
      (2 * Real.sinh t * Real.sin (β * t)) t := by
  have hne : (1 + β ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => β * t) β t := by
    simpa using (hasDerivAt_id t).const_mul β
  have hs := h1.sin
  have hc := h1.cos
  have hch := Real.hasDerivAt_cosh t
  have hsh := Real.hasDerivAt_sinh t
  have := (((hch.mul hs).sub ((hsh.const_mul β).mul hc)).const_mul 2).div_const (1 + β ^ 2)
  refine this.congr_deriv ?_
  field_simp
  ring

lemma aux_ds3e_int (β : ℝ) (hβ : 0 < β) :
    ∫ E in (2:ℝ)..(2 * Real.cosh (Real.pi / β)), Real.sin (β * Real.arcosh (E / 2)) =
      2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2) := by
  set G : ℝ → ℝ := fun t => 2 * (Real.cosh t * Real.sin (β * t) -
      β * Real.sinh t * Real.cos (β * t)) / (1 + β ^ 2) with hGdef
  have hX : (2:ℝ) ≤ 2 * Real.cosh (Real.pi / β) := by
    have := Real.one_le_cosh (Real.pi / β); linarith
  have hGc : Continuous G := by
    simp only [hGdef]; fun_prop
  have harc : ContinuousOn (fun E : ℝ => Real.arcosh (E / 2))
      (Set.Icc 2 (2 * Real.cosh (Real.pi / β))) := by
    apply Real.continuousOn_arcosh.comp (continuous_id.div_const 2).continuousOn
    intro E hE
    simp only [Set.mem_Ici, id]
    have := hE.1
    linarith
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun E => G (Real.arcosh (E / 2)))
    (f' := fun E => Real.sin (β * Real.arcosh (E / 2))) hX (hGc.comp_continuousOn harc) ?_ ?_
  · rw [key]
    have h1 : 2 * Real.cosh (Real.pi / β) / 2 = Real.cosh (Real.pi / β) := by ring
    rw [h1, Real.arcosh_cosh (by positivity), show (2:ℝ) / 2 = 1 by norm_num, Real.arcosh_zero]
    simp only [hGdef]
    rw [show β * (Real.pi / β) = Real.pi by field_simp]
    simp only [Real.sin_pi, Real.cos_pi, mul_zero, Real.sin_zero, Real.sinh_zero,
      Real.cosh_zero, Real.cos_zero]
    ring
  · intro E hE
    have hE1 : 1 < E / 2 := by have := hE.1; linarith
    have hd : HasDerivAt (fun E : ℝ => Real.arcosh (E / 2))
        ((√((E / 2) ^ 2 - 1))⁻¹ * (1 / 2)) E := by
      have h3 := Real.hasDerivAt_arcosh (x := E / 2) hE1
      have h2 : HasDerivAt (fun E : ℝ => E / 2) (1 / 2) E := by
        simpa using (hasDerivAt_id E).div_const 2
      have h4 := HasDerivAt.comp E h3 h2
      exact h4
    have := (aux_ds3e_G_deriv β (Real.arcosh (E / 2)) hβ).comp E hd
    refine this.congr_deriv ?_
    rw [Real.sinh_arcosh hE1.le]
    have hpos : 0 < √((E / 2) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
    generalize √((E / 2) ^ 2 - 1) = s at hpos ⊢
    have hs0 : s ≠ 0 := hpos.ne'
    field_simp
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX]
    exact Real.continuous_sin.comp_continuousOn (continuousOn_const.mul harc)

lemma aux_ds3e_rho0 (b : ℂ) (β : ℝ) (hb : b ^ 2 = Complex.I * (β : ℂ)) (E : ℝ) :
    rho0 b E = ((2 / Real.pi * Real.sinh (Real.pi * β) *
      Real.sin (β * Real.arcosh (E / 2)) : ℝ) : ℂ) := by
  unfold rho0
  rw [hb]
  have e1 : -Complex.I * (Real.pi : ℂ) * (Complex.I * (β : ℂ)) = ((Real.pi * β : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β : ℂ)) * Complex.I_sq
  have e2 : -Complex.I * (Complex.I * (β : ℂ)) * (Real.arcosh (E / 2) : ℂ) =
      ((β * Real.arcosh (E / 2) : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(β : ℂ) * (Real.arcosh (E / 2) : ℂ)) * Complex.I_sq
  rw [e1, e2, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
  push_cast
  ring

lemma aux_ds3e_E0 (b : ℂ) (β : ℝ) (hb : b ^ 2 = Complex.I * (β : ℂ)) :
    (E0 b).re = 2 * Real.cosh (Real.pi / β) := by
  unfold E0
  rw [hb]
  have e : (Real.pi : ℂ) * (Complex.I * (β : ℂ))⁻¹ = ((-(Real.pi / β) : ℝ) : ℂ) * Complex.I := by
    rw [mul_inv, Complex.inv_I]
    push_cast
    ring
  rw [e, Complex.cos_mul_I, ← Complex.ofReal_cosh, Real.cosh_neg]
  have : (2 : ℂ) * ((Real.cosh (Real.pi / β) : ℝ) : ℂ) = ((2 * Real.cosh (Real.pi / β) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

lemma aux_ds3e_norm (b : ℂ) (β S0 : ℝ) (hb : b ^ 2 = Complex.I * (β : ℂ)) :
    ‖(Real.exp (2 * S0) : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * b ^ 2) ^ 2 * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) ^ 2 /
          ((b ^ 2)⁻¹ - b ^ 2) ^ 2)‖ =
      Real.exp (2 * S0) * Real.sinh (Real.pi * β) ^ 2 * Real.sinh (Real.pi / β) ^ 2 /
        (β⁻¹ + β) ^ 2 := by
  rw [hb]
  have e1 : (Real.pi : ℂ) * (Complex.I * (β : ℂ)) = ((Real.pi * β : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : (Real.pi : ℂ) * (Complex.I * (β : ℂ))⁻¹ =
      ((-(Real.pi / β) : ℝ) : ℂ) * Complex.I := by
    rw [mul_inv, Complex.inv_I]; push_cast; ring
  have e3 : (Complex.I * (β : ℂ))⁻¹ - Complex.I * (β : ℂ) =
      ((-(β⁻¹ + β) : ℝ) : ℂ) * Complex.I := by
    rw [mul_inv, Complex.inv_I]; push_cast; ring
  rw [e1, e2, e3, Complex.sin_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sinh,
    ← Complex.ofReal_sinh]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, sq_abs, Real.sinh_neg, neg_sq, Real.abs_exp]
  ring

end DS3Micro

open DS3Micro

theorem solution (K : ℝ) (hK : 0 < K) (Z : ℂ → ℝ → ℂ)
    (hZ : ∀ (b : ℂ) (S0 : ℝ), InRegime b →
      ‖Z b S0‖ = K * ‖(Real.exp (2 * S0) : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * b ^ 2) ^ 2 * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) ^ 2 /
          ((b ^ 2)⁻¹ - b ^ 2) ^ 2)‖) :
    ∃ c : ℝ, ∀ (b : ℂ) (S0 : ℝ), InRegime b →
      SdSMicro b S0 = (Real.log ‖Z b S0‖ : ℂ) + (c : ℂ) := by
  refine ⟨-Real.log K - Real.log (Real.pi ^ 2 / 16), ?_⟩
  intro b S0 hreg
  obtain ⟨β, hβ, hb⟩ := hreg
  have hNeff : Neff b S0 = ((Real.exp S0 * (2 / Real.pi * Real.sinh (Real.pi * β)) *
      (2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2)) : ℝ) : ℂ) := by
    unfold Neff
    rw [aux_ds3e_E0 b β hb]
    simp_rw [aux_ds3e_rho0 b β hb]
    rw [← aux_ds3e_int β hβ, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_ofReal]
    congr 1
    funext E
    push_cast
    ring
  set N := Real.exp S0 * (2 / Real.pi * Real.sinh (Real.pi * β)) *
      (2 * β * Real.sinh (Real.pi / β) / (1 + β ^ 2)) with hN
  have hNpos : 0 < N := by
    have h1 : 0 < Real.sinh (Real.pi * β) := Real.sinh_pos_iff.mpr (by positivity)
    have h2 : 0 < Real.sinh (Real.pi / β) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  have hZb : ‖Z b S0‖ = K * (Real.pi ^ 2 / 16) * N ^ 2 := by
    rw [hZ b S0 ⟨β, hβ, hb⟩, aux_ds3e_norm b β S0 hb, hN]
    have hβ0 : β ≠ 0 := hβ.ne'
    have h1b : (1 + β ^ 2) ≠ 0 := by positivity
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have : (β⁻¹ + β) = (1 + β ^ 2) / β := by field_simp
    rw [this, show Real.exp (2 * S0) = Real.exp S0 ^ 2 by rw [sq, ← Real.exp_add]; ring_nf]
    field_simp
    ring
  have hlog : Real.log ‖Z b S0‖ =
      Real.log K + Real.log (Real.pi ^ 2 / 16) + 2 * Real.log N := by
    rw [hZb, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  unfold SdSMicro
  rw [hNeff, ← Complex.ofReal_log hNpos.le, hlog]
  push_cast
  ring
