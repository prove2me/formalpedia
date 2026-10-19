-- Prove2me | solution 1 for CohnElkies.harmonic_bottom_far_joint_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/80546f56-8641-45a0-b760-62477d8eb0b4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_tendsto_zero_bottom_of_ne
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_center_of_lower_of_abs_ge
import Theorems.Thm_CohnElkies_harmonic_stripPoissonKernel_zero_abs_integrable
import Theorems.Thm_CohnElkies_harmonic_bottom_normalized_height_tendsto
import Theorems.Thm_CohnElkies_harmonic_bottom_real_tendsto

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
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T in {T : ℝ | δ ≤ |T|},
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) - Complex.I * (ℓ : ℂ)
  let S : Set ℝ :=
    {T : ℝ | δ ≤ |T|}
  let C : ℝ :=
    1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const
      continuous_abs).measurableSet
  have hδarg : Real.pi * δ / 2 ≠ 0 := by
    exact (div_pos (mul_pos Real.pi_pos hδ)
      (by norm_num)).ne'
  have hcosh : 1 < Real.cosh (Real.pi * δ / 2) :=
    Real.one_lt_cosh.mpr hδarg
  have hC : 0 < C := by
    try dsimp [C]
    have hpositive := Real.cosh_pos (Real.pi * δ / 2)
    have hinv := (inv_lt_one₀ hpositive).mpr hcosh
    exact one_div_pos.mpr (by linarith)
  have hσ :
      Tendsto (fun z : ℂ => z.im / ℓ)
        (𝓝[U] z₀) (𝓝 (-1 : ℝ)) := by
    exact harmonic_bottom_normalized_height_tendsto
      hℓ s
  have hsreal :
      Tendsto Complex.re
        (𝓝[U] z₀) (𝓝 s) :=
    harmonic_bottom_real_tendsto s
  have hlower :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        -1 < z.im / ℓ := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    have hzbelow : -ℓ < z.im := hz.1
    apply (lt_div_iff₀ hℓ).2
    simpa using! hzbelow
  have hupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        z.im / ℓ ≤ 0 := by
    have hneg := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact hneg.mono (fun z hz => hz.le)
  have hrealbound :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        |z.re| ≤ |s| + 1 := by
    have hball := hsreal.eventually
      (Metric.ball_mem_nhds s
        (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hball]
      with z hz
    have hsmall : |z.re - s| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using! hz
    have htriangle := abs_add_le
      (z.re - s) s
    have heq : z.re - s + s = z.re := by ring
    rw [heq] at htriangle
    linarith
  have hkzero := stripPoissonKernel_integrable
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)
  have hmoment :=
    harmonic_stripPoissonKernel_zero_abs_integrable
  have hmajor : Integrable
      (fun T : ℝ =>
        C *
          ((A * (2 + |s|)) *
              stripPoissonKernel 0 T +
            (A * ℓ) *
              (stripPoissonKernel 0 T * |T|))) := by
    exact
      ((hkzero.const_mul
        (A * (2 + |s|))).add
        (hmoment.const_mul (A * ℓ))).const_mul C
  have hmeas :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        AEStronglyMeasurable
          (S.indicator
            (fun T : ℝ =>
              stripPoissonKernel (z.im / ℓ) T *
                b (z.re - ℓ * T))) := by
    filter_upwards [] with z
    have hk : Measurable
        (fun T : ℝ =>
          stripPoissonKernel (z.im / ℓ) T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    have hbT : Measurable
        (fun T : ℝ => b (z.re - ℓ * T)) := by
      exact hb.measurable.comp (by fun_prop)
    exact ((hk.mul hbT).aestronglyMeasurable).indicator hS
  have hdom :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        ∀ᵐ T : ℝ,
          ‖S.indicator
              (fun T : ℝ =>
                stripPoissonKernel (z.im / ℓ) T *
                  b (z.re - ℓ * T)) T‖ ≤
            C *
              ((A * (2 + |s|)) *
                  stripPoissonKernel 0 T +
                (A * ℓ) *
                  (stripPoissonKernel 0 T * |T|)) := by
    filter_upwards [hlower, hupper, hrealbound]
      with z hzbelow hzupper hzreal
    filter_upwards [] with T
    by_cases hT : T ∈ S
    · rw [Set.indicator_of_mem hT]
      have hkernel :=
        stripPoissonKernel_le_center_of_lower_of_abs_ge
          hzbelow hzupper hδ
          (show δ ≤ |T| from hT)
      have hkpos := stripPoissonKernel_pos
        hzbelow (by linarith) T
      have hzero := stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T
      have htri := abs_sub z.re (ℓ * T)
      have hmul : |ℓ * T| = ℓ * |T| := by
        rw [abs_mul, abs_of_pos hℓ]
      rw [hmul] at htri
      have hdata :
          |b (z.re - ℓ * T)| ≤
            A * (2 + |s| + ℓ * |T|) := by
        calc
          |b (z.re - ℓ * T)| ≤
              A * (1 + |z.re - ℓ * T|) :=
            hbound _
          _ ≤ A * (2 + |s| + ℓ * |T|) := by
            apply mul_le_mul_of_nonneg_left _ hA
            linarith
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos hkpos, Real.norm_eq_abs]
      change
        stripPoissonKernel (z.im / ℓ) T *
          |b (z.re - ℓ * T)| ≤ _
      calc
        stripPoissonKernel (z.im / ℓ) T *
            |b (z.re - ℓ * T)| ≤
          (C * stripPoissonKernel 0 T) *
            (A * (2 + |s| + ℓ * |T|)) := by
          exact mul_le_mul hkernel hdata
            (abs_nonneg _)
            (mul_nonneg hC.le hzero.le)
        _ = C *
              ((A * (2 + |s|)) *
                  stripPoissonKernel 0 T +
                (A * ℓ) *
                  (stripPoissonKernel 0 T * |T|)) := by
          ring
    · rw [Set.indicator_of_notMem hT, norm_zero]
      have hzero := stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T
      exact mul_nonneg hC.le
        (add_nonneg
          (mul_nonneg (by positivity) hzero.le)
          (mul_nonneg (by positivity)
            (mul_nonneg hzero.le (abs_nonneg T))))
  have hpoint :
      ∀ᵐ T : ℝ,
        Tendsto
          (fun z : ℂ =>
            S.indicator
              (fun T : ℝ =>
                stripPoissonKernel (z.im / ℓ) T *
                  b (z.re - ℓ * T)) T)
          (𝓝[U] z₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with T
    by_cases hT : T ∈ S
    · have hTne : T ≠ 0 := by
        intro hzero
        subst T
        have hbad : δ ≤ (0 : ℝ) := by
          simpa [S] using! hT
        linarith
      simp_rw [Set.indicator_of_mem hT]
      have hkernel :=
        (stripPoissonKernel_tendsto_zero_bottom_of_ne
          hTne).comp hσ
      have hcont : Continuous
          (fun z : ℂ => b (z.re - ℓ * T)) := by
        exact hb.comp (by fun_prop)
      have hdatum :
          Tendsto
            (fun z : ℂ => b (z.re - ℓ * T))
            (𝓝[U] z₀)
            (𝓝 (b (s - ℓ * T))) := by
        convert! hcont.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds using 1;
            simp [z₀]
      simpa using! hkernel.mul hdatum
    · simpa [Set.indicator_of_notMem hT] using!
        (tendsto_const_nhds :
          Tendsto (fun _ : ℂ => (0 : ℝ))
            (𝓝[U] z₀) (𝓝 (0 : ℝ)))
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ))
      (fun T : ℝ =>
        C *
          ((A * (2 + |s|)) *
              stripPoissonKernel 0 T +
            (A * ℓ) *
              (stripPoissonKernel 0 T * |T|)))
      hmeas hdom hmajor hpoint
  simpa [U, z₀, S, integral_indicator hS] using! hDCT
end CohnElkies
