-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredPolynomial_centralGaussianError_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/ff3507e1-1d1b-4622-aff9-b08662fce595

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integrable
import Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_stationary_gaussian_error_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (P : ℂ → ℂ)
    (hsource : Integrable (fun T : ℝ =>
      saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ))))
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + Complex.I * (u : ℂ)) -
        P (Complex.I * (u : ℂ))‖ ≤
          p * ‖P (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ)) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              P (Complex.I * (u : ℂ)))‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖P (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  have _hR : 0 ≤ R := hR
  let z : ℂ := Complex.I * (u : ℂ)
  let c : ℝ :=
    (2 * q + (1 + 2 * q) * p) * ‖P z‖
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hgaussian := saddleSourceGaussianKernel_integrable hℓ hV
  have hgaussianPoly : Integrable (fun T : ℝ =>
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z) :=
    hgaussian.ofReal.mul_const (P z)
  have hintegrable : Integrable (fun T : ℝ =>
      saddleSourceCenteredEnvelope ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T *
        P ((T : ℂ) + z) -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z) := by
    exact hsource.sub hgaussianPoly
  have hmajor : Integrable
      (fun T : ℝ => c * saddleSourceGaussianKernel ε ℓ u T) :=
    hgaussian.const_mul c
  have hpoint : ∀ T ∈ Icc (-R) R,
      ‖saddleSourceCenteredEnvelope ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T *
        P ((T : ℂ) + z) -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z‖ ≤
        c * saddleSourceGaussianKernel ε ℓ u T := by
    intro T hT
    have hTabs : |T| ≤ R :=
      (abs_le).mpr ⟨hT.1, hT.2⟩
    have hthird := hcubic T hTabs
    have hsmall :
        (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
          |T| ^ 3 ≤ 1 := hthird.trans hqone
    have henv :=
      saddleSourceCenteredEnvelope_stationary_gaussian_error_le
        hε hℓ hu horder hmargin T hsmall
    have henvq :
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
          2 * saddleSourceGaussianKernel ε ℓ u T * q := by
      calc
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
          2 * saddleSourceGaussianKernel ε ℓ u T *
            ((ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
              |T| ^ 3) := henv
        _ ≤ 2 * saddleSourceGaussianKernel ε ℓ u T * q := by
          exact mul_le_mul_of_nonneg_left hthird (by
            unfold saddleSourceGaussianKernel
            positivity)
    have hpolyT :
        ‖P ((T : ℂ) + z) - P z‖ ≤ p * ‖P z‖ := by
      exact hpoly T hTabs
    have hpolynorm :
        ‖P ((T : ℂ) + z)‖ ≤ (1 + p) * ‖P z‖ := by
      calc
        ‖P ((T : ℂ) + z)‖ =
          ‖(P ((T : ℂ) + z) - P z) + P z‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖P ((T : ℂ) + z) - P z‖ + ‖P z‖ :=
          norm_add_le _ _
        _ ≤ p * ‖P z‖ + ‖P z‖ := by
          gcongr
        _ = (1 + p) * ‖P z‖ := by ring
    have hg : 0 ≤ saddleSourceGaussianKernel ε ℓ u T := by
      unfold saddleSourceGaussianKernel
      exact (Real.exp_pos _).le
    have hdecomp :
        saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + z) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z =
          (saddleSourceCenteredEnvelope ε ℓ u
              (saddleSourceStationaryLogRadius ε ℓ u) T -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
              P ((T : ℂ) + z) +
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              (P ((T : ℂ) + z) - P z) := by
      ring
    rw [hdecomp]
    calc
      ‖(saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
            P ((T : ℂ) + z) +
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
            (P ((T : ℂ) + z) - P z)‖ ≤
        ‖(saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
            P ((T : ℂ) + z)‖ +
          ‖(saddleSourceGaussianKernel ε ℓ u T : ℂ) *
            (P ((T : ℂ) + z) - P z)‖ :=
          norm_add_le _ _
      _ = ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ *
            ‖P ((T : ℂ) + z)‖ +
          saddleSourceGaussianKernel ε ℓ u T *
            ‖P ((T : ℂ) + z) - P z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hg]
      _ ≤ (2 * saddleSourceGaussianKernel ε ℓ u T * q) *
            ((1 + p) * ‖P z‖) +
          saddleSourceGaussianKernel ε ℓ u T *
            (p * ‖P z‖) := by
          gcongr
      _ = c * saddleSourceGaussianKernel ε ℓ u T := by
        try dsimp [c]
        ring
  have hcomparison := setIntegral_mono_on
    hintegrable.norm.integrableOn hmajor.integrableOn
      measurableSet_Icc hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * saddleSourceGaussianKernel ε ℓ u T) := by
    exact Filter.Eventually.of_forall (fun T =>
      mul_nonneg hc (Real.exp_pos _).le)
  calc
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ)) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              P (Complex.I * (u : ℂ)))‖ ≤
      ∫ T : ℝ in Icc (-R) R,
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + z) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z‖ := by
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ T : ℝ in Icc (-R) R,
      c * saddleSourceGaussianKernel ε ℓ u T := hcomparison
    _ ≤ ∫ T : ℝ,
      c * saddleSourceGaussianKernel ε ℓ u T :=
        setIntegral_le_integral hmajor hnonnegative
    _ = (2 * q + (1 + 2 * q) * p) *
        ‖P (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
      rw [integral_const_mul]
end CohnElkies
