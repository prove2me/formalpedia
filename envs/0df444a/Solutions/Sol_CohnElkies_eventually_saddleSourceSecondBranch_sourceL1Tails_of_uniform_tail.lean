-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_sourceL1Tails_of_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/c1f3ae1d-6de3-42c4-932c-6dee0b312ebe

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
import Theorems.Thm_CohnElkies_exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound

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
    (hweighted :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Integrable
              (fun T : ℝ => saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T)))
    (htail :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ κ : ℝ, 0 < κ →
          ∀ᶠ ℓ : ℝ in atTop,
            ∀ δ : ℝ, ε / 2 ≤ δ →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping
                        ε ℓ (1 + δ) T)) < κ) :
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
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    hweighted, htail]
    with ε hε horder hvariance hweight htail'
  change 0 < ε at hε
  obtain ⟨Cp, hCp, hplus⟩ :=
    exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
      hε horder
  obtain ⟨Cm, hCm, hminus⟩ :=
    exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
      hε horder
  intro κ hκ
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htail' (κ / Cp) (div_pos hκ hCp),
    htail' (κ / Cm) (div_pos hκ hCm)]
    with ℓ hℓ hp hm
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hu : -1 < u := by
    try dsimp [u]
    nlinarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    nlinarith
  have hV : 0 < V := by
    try dsimp [V, u]
    exact hvariance ℓ hℓ δ hδ
  have hs : 0 < Real.sqrt (ℓ * V) := by positivity
  have hweighted' := hweight ℓ hℓ δ hδ
  have hpnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cp := by
    simpa [R, V, u] using! hp δ hδ
  have hmnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cm := by
    simpa [R, V, u] using! hm δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (beta_pos hε).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hbound := hplus ℓ hℓ u hu v R hweighted'
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) <
        κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cp) := by
          gcongr
      _ = κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCp.ne']
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := beta_pos hε
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      nlinarith
    have hbound := hminus ℓ hℓ u huminus v R hweighted'
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) <
        κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cm) := by
          gcongr
      _ = κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCm.ne']
end CohnElkies
