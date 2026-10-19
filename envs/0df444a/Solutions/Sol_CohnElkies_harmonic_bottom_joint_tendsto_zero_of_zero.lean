-- Prove2me | solution 1 for CohnElkies.harmonic_bottom_joint_tendsto_zero_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/05c8db24-9266-4cad-8fb5-8b1376f5564a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_lt_one
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_stripPoissonKernel_lower_product_integrable
import Theorems.Thm_CohnElkies_harmonic_bottom_normalized_height_tendsto
import Theorems.Thm_CohnElkies_harmonic_bottom_real_tendsto
import Theorems.Thm_CohnElkies_harmonic_bottom_far_joint_tendsto_zero

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hcentral : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b (t - ℓ * T)))
    (s : ℝ) (hszero : b s = 0) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) - Complex.I * (ℓ : ℂ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨η, hη, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp hb.continuousAt)
      (ε / 2) hhalf
  let δ : ℝ := η / (2 * ℓ)
  have hδ : 0 < δ := by
    try dsimp [δ]
    positivity
  let S : Set ℝ := {T : ℝ | δ ≤ |T|}
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const
      continuous_abs).measurableSet
  have hfar :=
    harmonic_bottom_far_joint_tendsto_zero
      hℓ hb hA hbound s hδ
  have hfarevent :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        ‖∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ < ε / 2 := by
    have hmetric :=
      (Metric.tendsto_nhds.mp hfar)
        (ε / 2) hhalf
    filter_upwards [hmetric] with z hz
    simpa [U, z₀, S, dist_zero_right] using! hz
  have hlower :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        -1 < z.im / ℓ := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    apply (lt_div_iff₀ hℓ).2
    simpa using! hz.1
  have hσ := harmonic_bottom_normalized_height_tendsto
    hℓ s
  have hupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        z.im / ℓ ≤ 0 := by
    have h := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact h.mono (fun z hz => hz.le)
  have hreal := harmonic_bottom_real_tendsto
    (ℓ := ℓ) s
  have hrealclose :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        |z.re - s| < η / 2 := by
    have hball := hreal.eventually
      (Metric.ball_mem_nhds s (half_pos hη))
    filter_upwards [hball]
      with z hz
    simpa [Metric.mem_ball, Real.dist_eq] using! hz
  filter_upwards [hlower, hupper,
    hfarevent, hrealclose]
    with z hzbelow hzupper hzfar hzreal
  have hzabove : z.im / ℓ < 1 := by linarith
  have hg : Continuous
      (fun T : ℝ => b (z.re - ℓ * T)) :=
    hb.comp (by fun_prop)
  have hproduct :=
    stripPoissonKernel_lower_product_integrable
      hzbelow hzupper hg (hcentral z.re)
  have hk := stripPoissonKernel_integrable
    hzbelow hzabove
  have hmajor : Integrable
      (fun T : ℝ =>
        (ε / 2) * stripPoissonKernel
          (z.im / ℓ) T) :=
    hk.const_mul (ε / 2)
  have hpositive :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ =>
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T) := by
    filter_upwards [] with T
    exact mul_nonneg hhalf.le
      (stripPoissonKernel_pos
        hzbelow hzabove T).le
  have hnear :
      ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤ ε / 2 := by
    calc
      ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤
        ∫ T in Sᶜ,
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T := by
        apply norm_integral_le_of_norm_le
          hmajor.integrableOn
        filter_upwards [ae_restrict_mem hS.compl]
          with T hT
        have hTsmall : |T| < δ := by
          have hnot : ¬ δ ≤ |T| := by
            intro hge
            exact hT (show T ∈ S from hge)
          exact lt_of_not_ge hnot
        have hscaled : ℓ * |T| < η / 2 := by
          try dsimp [δ] at hTsmall
          have hm := mul_lt_mul_of_pos_left
            hTsmall hℓ
          have heq : ℓ * (η / (2 * ℓ)) =
              η / 2 := by
            field_simp [hℓ.ne']
          rw [heq] at hm
          exact hm
        have htriangle := abs_sub
          (z.re - s) (ℓ * T)
        have hmul : |ℓ * T| = ℓ * |T| := by
          rw [abs_mul, abs_of_pos hℓ]
        rw [hmul] at htriangle
        have harg :
            |(z.re - ℓ * T) - s| < η := by
          have hring :
              (z.re - ℓ * T) - s =
                (z.re - s) - ℓ * T := by ring
          rw [hring]
          linarith
        have hbdist :
            dist (z.re - ℓ * T) s < η := by
          rw [Real.dist_eq]
          exact harg
        have hbsmall := hcontrol hbdist
        have hbabs :
            |b (z.re - ℓ * T)| < ε / 2 := by
          simpa [Real.dist_eq, hszero] using! hbsmall
        have hkpos := stripPoissonKernel_pos
          hzbelow hzabove T
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_pos hkpos, Real.norm_eq_abs]
        nlinarith [mul_nonneg hkpos.le
          (sub_nonneg.mpr hbabs.le)]
      _ ≤ ∫ T : ℝ,
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T :=
        setIntegral_le_integral
          hmajor hpositive
      _ = (ε / 2) *
          stripBottomMass (z.im / ℓ) := by
        rw [integral_const_mul,
          integral_stripPoissonKernel
            hzbelow hzabove]
      _ ≤ ε / 2 := by
        have hmass :=
          (stripBottomMass_lt_one hzbelow).le
        nlinarith [mul_nonneg hhalf.le
          (sub_nonneg.mpr hmass)]
  have hsplit := integral_add_compl hS hproduct
  rw [dist_zero_right]
  calc
    ‖∫ T : ℝ,
        stripPoissonKernel (z.im / ℓ) T *
          b (z.re - ℓ * T)‖ =
      ‖(∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) +
        (∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))‖ := by
      rw [hsplit]
    _ ≤ ‖∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ +
        ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ :=
      norm_add_le _ _
    _ < ε := by linarith
end CohnElkies
