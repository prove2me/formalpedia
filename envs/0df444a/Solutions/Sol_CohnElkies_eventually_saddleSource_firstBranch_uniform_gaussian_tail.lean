-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_firstBranch_uniform_gaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/89aa3746-9b81-4048-9a70-2b11a63f39be

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_firstBranch_pos
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_normalized_tail_le
import Theorems.Thm_CohnElkies_tendsto_saddleSourceGaussianNormalizedTailMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ,
            -1 < u → u ≤ 1 + ε / 2 →
              Real.log ℓ / 4 ≤ ℓ * (1 + u) →
                Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    saddleSourceGaussianKernel ε ℓ u T) < κ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards [hnear.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hvariance
  change 0 < ε at hε
  intro κ hκ
  let U : ℝ := 2 + ε / 2
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hlog : Tendsto (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hdecay :=
    (tendsto_saddleSourceGaussianNormalizedTailMajorant.comp
      hlog).eventually (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (6 * U / ε),
    hlog.eventually (eventually_ge_atTop (0 : ℝ)),
    hdecay] with ℓ hℓ hthreshold hlognonneg hdecayℓ
  intro u hulower huupper hlogscale
  let η : ℝ := 1 + u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let z : ℝ := (ℓ * η) ^ (1 / 12 : ℝ)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηupper : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hV : 0 < V :=
    hvariance ℓ hℓ u hulower huupper
  have hmargin' :
      ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
        0 ≤ shortMargin ε a := by
    intro a ha
    have h := hmargin a ha
    linarith
  have hvar :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin'
  have hvarupper : 2 * ε ≤ U * V := by
    have hproduct :=
      mul_le_mul_of_nonneg_right hηupper hV.le
    change 2 * ε ≤ η * V at hvar
    exact hvar.trans hproduct
  have hthreshold' : 6 * U ≤ ℓ * ε := by
    have h := (div_le_iff₀ hε).mp hthreshold
    nlinarith
  have hlarge : 12 ≤ ℓ * V := by
    have hproduct := mul_le_mul_of_nonneg_left
      hvarupper hℓ.le
    have hmain : U * 12 ≤ U * (ℓ * V) := by
      nlinarith
    by_contra hnot
    have hlt : ℓ * V < 12 := lt_of_not_ge hnot
    have hcontradiction := mul_lt_mul_of_pos_left hlt hU
    linarith
  have hz : 0 ≤ z := by
    try dsimp [z]
    exact Real.rpow_nonneg
      (mul_nonneg hℓ.le hη.le) _
  have hgaussian := saddleSourceGaussianKernel_normalized_tail_le
    (ε := ε) (ℓ := ℓ) (u := u) (z := z)
    hℓ hV hz hlarge
  have hpower :
      (Real.log ℓ / 4) ^ (1 / 6 : ℝ) ≤ z ^ 2 := by
    have hmono := Real.rpow_le_rpow hlognonneg hlogscale
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have hsquare : z ^ 2 = (ℓ * η) ^ (1 / 6 : ℝ) := by
      try dsimp [z]
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg hℓ.le hη.le)]
      congr 1
      norm_num
    rw [hsquare]
    exact hmono
  calc
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceFirstBranchCentralRadius ε ℓ u),
        saddleSourceGaussianKernel ε ℓ u T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8) := by
      simpa [saddleSourceFirstBranchCentralRadius,
        V, η, z] using! hgaussian
    _ ≤ saddleSourceGaussianNormalizedTailMajorant
      (Real.log ℓ / 4) := by
      unfold saddleSourceGaussianNormalizedTailMajorant
      gcongr
    _ < κ := hdecayℓ
end CohnElkies
