-- Prove2me | solution 1 for CohnElkies.stripRegularizedOuter_differentiableAt_of_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/29badd66-dcc9-4fbd-9c7a-f8673848fc56

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernelDeriv_continuous
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernelDeriv_local_bound
import Theorems.Thm_CohnElkies_stripRegularizedOuter_integrable_of_exp_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) * b y)) :
    DifferentiableAt ℂ (stripRegularizedOuter ℓ b) z := by
  obtain ⟨S, hS, C, hC, hderivbound⟩ :=
    stripRegularizedHolomorphicPoissonKernelDeriv_local_bound hℓ hz
  have hstrip :
      Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z := by
    have him : Continuous (fun w : ℂ => w.im) := by
      fun_prop
    exact (isOpen_Ioo.preimage him).mem_nhds hz
  have hneighborhood :
      S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ) ∈ 𝓝 z :=
    inter_mem hS hstrip
  have hboundaryabs :
      Integrable
        (fun y : ℝ =>
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)] using! hboundary.norm
  have hboundintegrable :
      Integrable
        (fun y : ℝ =>
          C * (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|)) :=
    hboundaryabs.const_mul C
  have hFmeas :
      ∀ᶠ w : ℂ in 𝓝 z,
        AEStronglyMeasurable
          (fun y : ℝ =>
            stripRegularizedHolomorphicPoissonKernel ℓ w y *
              (b y : ℂ)) := by
    filter_upwards [hstrip] with w hw
    exact
      (stripRegularizedOuter_integrable_of_exp_integrable
        hℓ hw b hb hboundary).aestronglyMeasurable
  have hFint :
      Integrable
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ)) :=
    stripRegularizedOuter_integrable_of_exp_integrable hℓ hz b hb hboundary
  have hGmeas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y *
            (b y : ℂ)) := by
    have hreal := hb.measurable
    have hcast :
        Measurable (fun y : ℝ => (b y : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hreal
    exact
      ((stripRegularizedHolomorphicPoissonKernelDeriv_continuous
        hℓ hz).measurable.mul hcast).aestronglyMeasurable
  have hdominated :
      ∀ᵐ y : ℝ, ∀ w ∈ S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ),
        ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
          (b y : ℂ)‖ ≤
            C *
              (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
                |b y|) := by
    filter_upwards [] with y
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ *
          |b y| ≤
        (C * Real.exp (-(Real.pi / (2 * ℓ)) * |y|)) *
          |b y| :=
        mul_le_mul_of_nonneg_right
          (hderivbound w hw.1 y) (abs_nonneg _)
      _ = C *
          (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|) := by
        ring
  have hdiff :
      ∀ᵐ y : ℝ, ∀ w ∈ S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ),
        HasDerivAt
          (fun v : ℂ =>
            stripRegularizedHolomorphicPoissonKernel ℓ v y *
              (b y : ℂ))
          (stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
            (b y : ℂ)) w := by
    filter_upwards [] with y
    intro w hw
    exact
      (stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
        hℓ hw.2 y).mul_const (b y : ℂ)
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w : ℂ => fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ w y *
          (b y : ℂ))
      (F' := fun w : ℂ => fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
          (b y : ℂ))
      (bound := fun y : ℝ =>
        C * (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
          |b y|))
      hneighborhood hFmeas hFint hGmeas
      hdominated hboundintegrable hdiff
  unfold stripRegularizedOuter
  exact hresult.2.differentiableAt
end CohnElkies
