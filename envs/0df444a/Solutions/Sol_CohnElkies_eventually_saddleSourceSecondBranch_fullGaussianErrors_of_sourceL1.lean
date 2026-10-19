-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_fullGaussianErrors_of_sourceL1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/a68e032f-0cf5-4ed3-8082-5c258f161769

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral_pos
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_integrable
import Theorems.Thm_CohnElkies_saddleSourceGaussianMinusIntegrand_integrable
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_saddleSourceCenteredPlusIntegrand_integrable
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_integrable
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_centralGaussianErrors
import Theorems.Thm_CohnElkies_saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_gaussianL1Tails

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hsource :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ κ : ℝ, 0 < κ →
          ∀ᶠ ℓ : ℝ in atTop,
            ∀ δ : ℝ, ε / 2 ≤ δ →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  ‖saddleSourceCenteredPlusIntegrand
                      ε ℓ (1 + δ)
                      (saddleSourceStationaryLogRadius
                        ε ℓ (1 + δ)) T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  ‖saddleSourceCenteredMinusIntegrand
                      ε ℓ (1 + δ)
                      (saddleSourceStationaryLogRadius
                        ε ℓ (1 + δ)) T‖) <
                κ * ‖minusPolynomial ε
                  (Complex.I * ((1 + δ : ℝ) : ℂ))‖)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, ε / 2 ≤ δ →
          (‖(∫ T : ℝ,
              saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianPlusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖plusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
          (‖(∫ T : ℝ,
              saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianMinusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖minusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_centralGaussianErrors,
    hsource,
    eventually_saddleSourceSecondBranch_gaussianL1Tails]
    with ε hε horder hvariance hcentral hsource' hgaussian
  change 0 < ε at hε
  let a : ℝ := Real.sqrt (2 * Real.pi) / 8
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcentral (1 / 4 : ℝ) (by norm_num),
    hsource' a ha, hgaussian a ha]
    with ℓ hℓ hc hs hg
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  have hu : -1 < u := by
    try dsimp [u]
    nlinarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    nlinarith
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u := by
    try dsimp [u]
    exact hvariance ℓ hℓ δ hδ
  have hG := saddleSourceGaussianKernel_integral_pos hℓ hV
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  obtain ⟨hcplus, hcminus⟩ := hc δ hδ
  obtain ⟨hsplus, hsminus⟩ := hs δ hδ
  obtain ⟨hgplus, hgminus⟩ := hg δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (beta_pos hε).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredPlusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianPlusIntegrand ε ℓ u)
        (saddleSourceCenteredPlusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianPlusIntegrand_integrable hℓ hV)
        hℓ hV hcplus hsplus hgplus
    change
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T)
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        nlinarith [mul_pos hden hG]
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := beta_pos hε
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      nlinarith
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredMinusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianMinusIntegrand ε ℓ u)
        (saddleSourceCenteredMinusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianMinusIntegrand_integrable hℓ hV)
        hℓ hV hcminus hsminus hgminus
    change
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T)
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        nlinarith [mul_pos hden hG]
end CohnElkies
