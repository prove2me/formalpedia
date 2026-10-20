-- Prove2me | solution 2 for CohnElkies.stripRegularizedOuter_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:40:11.274285+00:00
-- url     : https://prove2.me/submissions/9c9713dd-825b-474f-898a-ced5a7d0001f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
theorem h47s_re_aux (X θ L : ℝ) (hL : 0 < L) (hθ : 0 < Real.sin θ) :
    (Complex.I * ((Complex.exp ((X : ℂ) + Complex.I * (θ : ℂ)) + 1) /
        (Complex.exp ((X : ℂ) + Complex.I * (θ : ℂ)) - 1)) / 4 / (L : ℂ)).re =
      Real.sin θ / (4 * (Real.cosh X - Real.cos θ)) / L := by
  have hE : Complex.exp ((X : ℂ) + Complex.I * (θ : ℂ)) =
      ((Real.exp X * Real.cos θ : ℝ) : ℂ) + ((Real.exp X * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_add, mul_comm Complex.I, Complex.exp_mul_I]
    push_cast
    rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [hE]
  set a := Real.exp X * Real.cos θ with ha
  set b := Real.exp X * Real.sin θ with hb
  have hbpos : 0 < b := mul_pos (Real.exp_pos X) hθ
  have hcosh : Real.cosh X = (Real.exp X + Real.exp (-X)) / 2 := Real.cosh_eq X
  have hden : 0 < (a - 1) ^ 2 + b ^ 2 := by positivity
  have hexp : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
  have hc : Real.cosh X - Real.cos θ = ((a - 1) ^ 2 + b ^ 2) / (2 * Real.exp X) := by
    rw [hcosh, ha, hb]
    have hex := Real.exp_pos X
    field_simp
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this, hexp]
  rw [hc]
  have hL' : (L : ℂ) = ((L : ℝ) : ℂ) := rfl
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.normSq_apply]
  norm_num
  have hex := Real.exp_pos X
  field_simp
  rw [hb]; ring

theorem h47s_pt {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hσbelow : -1 < σ) (hσabove : σ < 1) (s y : ℝ) :
    (CohnElkies.stripRegularizedHolomorphicPoissonKernel ℓ
        ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y).re =
      CohnElkies.stripPoissonKernel σ ((s - y) / ℓ) / ℓ := by
  have hθ : 0 < Real.sin (CohnElkies.stripAngle σ) := by
    unfold CohnElkies.stripAngle
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := Real.pi_pos; nlinarith
    · have := Real.pi_pos; nlinarith
  have hw : (Real.pi : ℂ) * ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ) - (y : ℂ) + Complex.I * (ℓ : ℂ)) /
      (2 * (ℓ : ℂ)) = ((Real.pi * ((s - y) / ℓ) / 2 : ℝ) : ℂ) +
        Complex.I * ((CohnElkies.stripAngle σ : ℝ) : ℂ) := by
    unfold CohnElkies.stripAngle
    have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
    push_cast
    field_simp
    ring
  unfold CohnElkies.stripRegularizedHolomorphicPoissonKernel CohnElkies.stripHolomorphicPoissonKernel
  rw [Complex.add_re, hw, h47s_re_aux _ _ _ hℓ hθ]
  unfold CohnElkies.stripPoissonKernel
  have h0 : ((if 0 ≤ y then Complex.I else -Complex.I) / ((4 * ℓ : ℝ) : ℂ)).re = 0 := by
    split_ifs <;> simp [Complex.div_re]
  rw [h0, add_zero]

theorem solution
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (s : ℝ) (b : ℝ → ℝ)
    (houter : Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ))) :
    (stripRegularizedOuter ℓ b
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) := by
  unfold stripRegularizedOuter
  rw [← RCLike.re_eq_complex_re, ← integral_re houter]
  have h1 : ∀ y : ℝ, RCLike.re (stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y * (b y : ℂ)) =
        stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y := by
    intro y
    rw [RCLike.re_eq_complex_re, Complex.re_mul_ofReal, h47s_pt hℓ hσbelow hσabove s y]
  simp_rw [h1]
  have h2 := Measure.integral_comp_mul_left (fun u : ℝ => stripPoissonKernel σ ((s - (s - u)) / ℓ) / ℓ * b (s - u)) ℓ
  have h3 := integral_sub_left_eq_self (fun y : ℝ => stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y) (μ := volume) s
  try simp only at h2 h3
  rw [h3] at h2
  have h4 : ∀ T : ℝ, stripPoissonKernel σ ((s - (s - ℓ * T)) / ℓ) / ℓ * b (s - ℓ * T) =
      ℓ⁻¹ * (stripPoissonKernel σ T * b (s - ℓ * T)) := by
    intro T
    have : (s - (s - ℓ * T)) / ℓ = T := by field_simp; ring
    rw [this]; field_simp
  simp_rw [h4, integral_const_mul] at h2
  rw [abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul] at h2
  have := mul_left_cancel₀ (inv_pos.mpr hℓ).ne' h2
  exact this.symm

