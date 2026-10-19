-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_central_radius_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/19038595-75af-4137-a172-ad91c5e2142a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceFloor_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_floor
import Theorems.Thm_CohnElkies_saddleSourceSecondBranch_central_radius_le

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
            saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) < κ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  have hfloorpos :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  intro κ hκ
  let A : ℝ :=
    1 / Real.sqrt (saddleSourceSecondBranchVarianceFloor ε)
  have htendsto :
      Tendsto (fun ℓ : ℝ => A * ℓ ^ (-(5 / 12 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 5 / 12)) using 1
    all_goals simp
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htendsto.eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hsmall
  intro δ hδ
  exact (saddleSourceSecondBranch_central_radius_le
    hℓ (hfloor ℓ hℓ δ hδ) hfloorpos).trans_lt hsmall
end CohnElkies
