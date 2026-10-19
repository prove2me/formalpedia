-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_centralGaussianErrors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/31d513d5-1e78-4b67-9486-7692ad1f82c9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_saddleSourceCenteredPlusIntegrand_centralGaussianError_le
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_centralGaussianError_le
import Theorems.Thm_CohnElkies_exists_plusPolynomial_uniform_central_window
import Theorems.Thm_CohnElkies_exists_minusPolynomial_uniform_central_window
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_cubic_window
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_central_radius_lt
import Theorems.Thm_CohnElkies_exists_saddleSource_central_error_tolerance

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianPlusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianMinusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_cubic_window,
    eventually_saddleSourceSecondBranch_central_radius_lt]
    with ε hε horder hmargin hvariance hcubic hradius
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a := by
    intro a ha
    have h := hmargin a ha
    nlinarith
  intro κ hκ
  obtain ⟨q, hq, hqone, hfactor⟩ :=
    exists_saddleSource_central_error_tolerance hκ
  obtain ⟨Rp, hRp, hplus⟩ :=
    exists_plusPolynomial_uniform_central_window hε hq
  obtain ⟨Rm, hRm, hminus⟩ :=
    exists_minusPolynomial_uniform_central_window hε hq
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcubic q hq,
    hradius Rp hRp,
    hradius Rm hRm]
    with ℓ hℓ hqc hsmallplus hsmallminus
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  have hδzero : 0 ≤ δ := by linarith
  have hu : -1 < u := by
    try dsimp [u]
    linarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    linarith
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u := by
    try dsimp [u]
    exact hvariance ℓ hℓ δ hδ
  have hR : 0 ≤ R := by
    try dsimp [R, saddleSourceSecondBranchCentralRadius]
    positivity
  have hphase : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q := by
    intro T hT
    have h := hqc δ hδ T hT
    have huarg : u - 1 = δ := by
      try dsimp [u]
      ring
    rw [huarg]
    exact h.le
  have hG : 0 < ∫ T : ℝ,
      saddleSourceGaussianKernel ε ℓ u T :=
    saddleSourceGaussianKernel_integral_pos hℓ hV
  constructor
  · have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖plusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hplus u hu.le T
        (hT.trans (hsmallplus δ hδ).le)
    have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (beta_pos hε).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hcentral :=
      saddleSourceCenteredPlusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    change
      ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredPlusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)
    exact hcentral.trans_lt (by gcongr)
  · have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hminus u huminus T
        (hT.trans (hsmallminus δ hδ).le)
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hbeta := beta_pos hε
      have hbound :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      nlinarith
    have hcentral :=
      saddleSourceCenteredMinusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    change
      ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredMinusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)
    exact hcentral.trans_lt (by gcongr)
end CohnElkies
