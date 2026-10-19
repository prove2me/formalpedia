-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_uniform_gaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/7062c2f1-3037-4bd7-8eac-6cc637f3e927

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceFloor_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_floor
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
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Real.sqrt
              (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                (saddleSourceSecondBranchCentralRadius
                  ε ℓ (1 + δ)),
                saddleSourceGaussianKernel ε ℓ (1 + δ) T) < κ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  intro κ hκ
  let V₀ : ℝ := saddleSourceSecondBranchVarianceFloor ε
  have hV₀ : 0 < V₀ :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  have hdecay :=
    tendsto_saddleSourceGaussianNormalizedTailMajorant.eventually
      (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 / V₀), hdecay]
    with ℓ hℓ hthreshold hdecayℓ
  intro δ hδ
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let z : ℝ := ℓ ^ (1 / 12 : ℝ)
  have hVlower : V₀ ≤ V :=
    hfloor ℓ hℓ δ hδ
  have hV : 0 < V := hV₀.trans_le hVlower
  have hlarge : 12 ≤ ℓ * V := by
    have hbase := (div_le_iff₀ hV₀).mp hthreshold
    calc
      12 ≤ ℓ * V₀ := by nlinarith
      _ ≤ ℓ * V :=
        mul_le_mul_of_nonneg_left hVlower hℓ.le
  have hz : 0 ≤ z := by
    try dsimp [z]
    exact Real.rpow_nonneg hℓ.le _
  have hgaussian := saddleSourceGaussianKernel_normalized_tail_le
    (ε := ε) (ℓ := ℓ) (u := 1 + δ) (z := z)
    hℓ hV hz hlarge
  have hsquare : z ^ 2 = ℓ ^ (1 / 6 : ℝ) := by
    try dsimp [z]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul hℓ.le]
    congr 1
    norm_num
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
        saddleSourceGaussianKernel ε ℓ (1 + δ) T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8) := by
      simpa [saddleSourceSecondBranchCentralRadius,
        V, z] using! hgaussian
    _ = saddleSourceGaussianNormalizedTailMajorant ℓ := by
      unfold saddleSourceGaussianNormalizedTailMajorant
      rw [hsquare]
    _ < κ := hdecayℓ
end CohnElkies
