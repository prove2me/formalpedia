-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceFirstBranch_sourceL1Tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/ab8134af-cbe6-49ef-a89a-98cb26d52aa0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_firstBranch_pos
import Theorems.Thm_CohnElkies_saddleSource_firstBranch_weighted_integrable
import Theorems.Thm_CohnElkies_eventually_saddleSource_firstBranch_uniform_tail
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
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  ‖saddleSourceCenteredPlusIntegrand ε ℓ u
                      (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * (u : ℂ))‖) ∧
              (1 + ε / 4 ≤ u →
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    ‖saddleSourceCenteredMinusIntegrand ε ℓ u
                        (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                  κ * ‖minusPolynomial ε
                    (Complex.I * (u : ℂ))‖) := by
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear :=
      (tendsto_id.mono_left
        (nhdsWithin_le_nhds :
          𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hnear] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, heps,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSource_firstBranch_uniform_tail]
    with ε hε hεsmall horder hmargin hvariance htail
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a := by
    intro a ha
    have h := hmargin a ha
    nlinarith
  obtain ⟨Cp, hCp, hplus⟩ :=
    exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
      hε horder
  obtain ⟨Cm, hCm, hminus⟩ :=
    exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
      hε horder
  intro κ hκ
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htail (κ / Cp) (div_pos hκ hCp),
    htail (κ / Cm) (div_pos hκ hCm)]
    with ℓ hℓ hp hm
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hV : 0 < V := hvariance ℓ hℓ u hu huupper
  have hs : 0 < Real.sqrt (ℓ * V) := by positivity
  have hweighted := saddleSource_firstBranch_weighted_integrable
    hε hεsmall hℓ hu huupper horder hmargin'
  have hpnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cp := by
    simpa [R, V, saddleSourceFirstBranchCentralRadius] using! hp u hu huupper hstar
  have hmnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cm := by
    simpa [R, V, saddleSourceFirstBranchCentralRadius] using! hm u hu huupper hstar
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (beta_pos hε).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hbound := hplus ℓ hℓ u hu v R hweighted
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
  · intro huminus
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := beta_pos hε
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      nlinarith
    have hbound := hminus ℓ hℓ u huminus v R hweighted
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
