-- Prove2me | solution 1 for CohnElkies.harmonic_upper_joint_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/27eaa845-c126-46d9-8dcc-66556d4c8b3d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_exponentialMajorant_of_nonneg
import Theorems.Thm_CohnElkies_harmonic_stripPoissonExponentialMajorant_abs_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_tendsto_zero_top
import Theorems.Thm_CohnElkies_harmonic_top_normalized_height_tendsto

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
    (s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) + Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) + Complex.I * (ℓ : ℂ)
  have hσ : Tendsto
      (fun z : ℂ => z.im / ℓ)
        (𝓝[U] z₀) (𝓝 (1 : ℝ)) :=
    harmonic_top_normalized_height_tendsto hℓ s
  have hreal : Tendsto Complex.re
      (𝓝[U] z₀) (𝓝 s) := by
    convert! Complex.continuous_re.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds using 1;
      simp [z₀]
  have hnonneg : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      0 ≤ z.im / ℓ := by
    have h := hσ.eventually
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    exact h.mono (fun z hz => hz.le)
  have habove : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      z.im / ℓ < 1 := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    apply (div_lt_iff₀ hℓ).2
    simpa using! hz.2
  have hrealbound : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      |z.re| ≤ |s| + 1 := by
    have hball := hreal.eventually
      (Metric.ball_mem_nhds s
        (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hball] with z hz
    have hsmall : |z.re - s| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using! hz
    have htri := abs_add_le (z.re - s) s
    have heq : z.re - s + s = z.re := by ring
    rw [heq] at htri
    linarith
  have hmajor : Integrable
      (fun T : ℝ =>
        (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|)) :=
    (stripPoissonExponentialMajorant_integrable.const_mul
      (A * (2 + |s|))).add
      (harmonic_stripPoissonExponentialMajorant_abs_integrable.const_mul
        (A * ℓ))
  have hmeas : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      AEStronglyMeasurable
        (fun T : ℝ =>
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) := by
    filter_upwards [] with z
    have hk : Measurable
        (fun T : ℝ => stripPoissonKernel (z.im / ℓ) T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    have hdatum : Measurable
        (fun T : ℝ => b (z.re - ℓ * T)) :=
      hb.measurable.comp (by fun_prop)
    exact (hk.mul hdatum).aestronglyMeasurable
  have hdom : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      ∀ᵐ T : ℝ,
        ‖stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤
          (A * (2 + |s|)) *
              stripPoissonExponentialMajorant T +
            (A * ℓ) *
              (stripPoissonExponentialMajorant T * |T|) := by
    filter_upwards [hnonneg, habove, hrealbound]
      with z hznonneg hzabove hzreal
    filter_upwards [] with T
    have hzbelow : -1 < z.im / ℓ := by linarith
    have hkpos := stripPoissonKernel_pos hzbelow hzabove T
    have hkbound :=
      stripPoissonKernel_le_exponentialMajorant_of_nonneg
        hznonneg hzabove T
    have hmajorpos : 0 ≤ stripPoissonExponentialMajorant T := by
      unfold stripPoissonExponentialMajorant
      positivity
    have htri := abs_sub z.re (ℓ * T)
    have hmul : |ℓ * T| = ℓ * |T| := by
      rw [abs_mul, abs_of_pos hℓ]
    rw [hmul] at htri
    have hdata :
        |b (z.re - ℓ * T)| ≤
          A * (2 + |s| + ℓ * |T|) := by
      calc
        |b (z.re - ℓ * T)| ≤
          A * (1 + |z.re - ℓ * T|) := hbound _
        _ ≤ A * (2 + |s| + ℓ * |T|) := by
          apply mul_le_mul_of_nonneg_left _ hA
          linarith
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos hkpos, Real.norm_eq_abs]
    calc
      stripPoissonKernel (z.im / ℓ) T *
          |b (z.re - ℓ * T)| ≤
        stripPoissonExponentialMajorant T *
          (A * (2 + |s| + ℓ * |T|)) :=
            mul_le_mul hkbound hdata
              (abs_nonneg _) hmajorpos
      _ = (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|) := by
            ring
  have hpoint : ∀ᵐ T : ℝ,
      Tendsto
        (fun z : ℂ =>
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
        (𝓝[U] z₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with T
    have hk :=
      (stripPoissonKernel_tendsto_zero_top T).comp hσ
    have hcont : Continuous
        (fun z : ℂ => b (z.re - ℓ * T)) :=
      hb.comp (by fun_prop)
    have hdatum : Tendsto
        (fun z : ℂ => b (z.re - ℓ * T))
        (𝓝[U] z₀) (𝓝 (b (s - ℓ * T))) := by
      convert! hcont.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds using 1;
          simp [z₀]
    simpa using! hk.mul hdatum
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ))
      (fun T : ℝ =>
        (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|))
      hmeas hdom hmajor hpoint
  simpa [U, z₀] using! h
end CohnElkies
