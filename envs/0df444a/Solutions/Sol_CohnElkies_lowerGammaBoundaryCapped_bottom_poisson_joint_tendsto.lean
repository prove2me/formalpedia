-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/51a35596-514e-48d9-8954-4926ef10e49d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
import Theorems.Thm_CohnElkies_stripPoissonKernel_lower_product_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_central_poisson_shift_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_abs_le_linear
import Theorems.Thm_CohnElkies_harmonic_bottom_normalized_height_tendsto
import Theorems.Thm_CohnElkies_harmonic_bottom_joint_tendsto_zero_of_zero

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
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ((d : ℝ) / 2)) T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
              (z.re - ((d : ℝ) / 2) * T))
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) -
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (lowerGammaBoundaryCapped
        ((d : ℝ) / 2) R D s)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let b : ℝ → ℝ := lowerGammaBoundaryCapped ℓ R D
  let b₀ : ℝ → ℝ := fun y => b y - b s
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ := (s : ℂ) - Complex.I * (ℓ : ℂ)
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  have hb : Continuous b :=
    lowerGammaBoundaryCapped_continuous hℓ R D
  have hb₀ : Continuous b₀ := by
    try dsimp [b₀]
    fun_prop
  obtain ⟨A, hA, hbound⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear hd R D
  let A₀ : ℝ := A + |b s|
  have hA₀ : 0 ≤ A₀ := by
    try dsimp [A₀]
    positivity
  have hbound₀ : ∀ y : ℝ,
      |b₀ y| ≤ A₀ * (1 + |y|) := by
    intro y
    have htriangle := abs_sub (b y) (b s)
    have hbmain : |b y| ≤ A * (1 + |y|) := by
      exact hbound y
    have hy : 0 ≤ |y| := abs_nonneg y
    have hbs : 0 ≤ |b s| := abs_nonneg _
    try dsimp [b₀, A₀]
    nlinarith [mul_nonneg hbs hy]
  have hcentral : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b (t - ℓ * T)) := by
    intro t
    exact lowerGammaBoundaryCapped_central_poisson_shift_integrable
      hd R D t
  have hkcentral := stripPoissonKernel_integrable
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)
  have hcentral₀ : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b₀ (t - ℓ * T)) := by
    intro t
    have hsub := (hcentral t).sub
      (hkcentral.mul_const (b s))
    convert! hsub using 1
    ext T
    try dsimp [b₀]
    ring
  have hzero := harmonic_bottom_joint_tendsto_zero_of_zero
    hℓ hb₀ hA₀ hbound₀ hcentral₀ s
      (show b₀ s = 0 by simp [b₀])
  have hσ := harmonic_bottom_normalized_height_tendsto
    hℓ s
  have hmasscontinuous : Continuous stripBottomMass := by
    unfold stripBottomMass
    fun_prop
  have hmass : Tendsto
      (fun z : ℂ => stripBottomMass (z.im / ℓ))
      (𝓝[U] z₀) (𝓝 (1 : ℝ)) := by
    convert! hmasscontinuous.continuousAt.tendsto.comp hσ
      using 1; norm_num [stripBottomMass]
  have hsum := hzero.add (hmass.mul_const (b s))
  have hσupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀, z.im / ℓ ≤ 0 := by
    have hevent := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact hevent.mono fun z hz => hz.le
  have heq :
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) =ᶠ[𝓝[U] z₀]
      (fun z : ℂ =>
        (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          stripBottomMass (z.im / ℓ) * b s) := by
    filter_upwards [self_mem_nhdsWithin, hσupper]
      with z hz hzupper
    have hzlower : -1 < z.im / ℓ := by
      apply (lt_div_iff₀ hℓ).2
      simpa using! hz.1
    have hzabove : z.im / ℓ < 1 := by linarith
    have hg₀ : Continuous
        (fun T : ℝ => b₀ (z.re - ℓ * T)) := by
      exact hb₀.comp (by fun_prop)
    have hprod₀ :=
      stripPoissonKernel_lower_product_integrable
        hzlower hzupper hg₀ (hcentral₀ z.re)
    have hk := stripPoissonKernel_integrable
      hzlower hzabove
    have hconst := hk.mul_const (b s)
    calc
      (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) =
        ∫ T : ℝ,
          (stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T) +
           stripPoissonKernel (z.im / ℓ) T * b s) := by
          congr 1
          funext T
          try dsimp [b₀]
          ring
      _ = (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          ∫ T : ℝ,
            stripPoissonKernel (z.im / ℓ) T * b s :=
        integral_add hprod₀ hconst
      _ = (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          stripBottomMass (z.im / ℓ) * b s := by
        rw [integral_mul_const,
          integral_stripPoissonKernel hzlower hzabove]
  have hresult := hsum.congr' heq.symm
  simpa [ℓ, b, U, z₀] using! hresult
end CohnElkies
