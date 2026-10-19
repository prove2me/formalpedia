-- Prove2me | solution 1 for CohnElkies.saddleSourceSecondBranch_central_radius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/5499b102-405a-461b-9bbc-8cb56d60b06b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSource_central_rpow_div_sqrt

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
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hfloor : saddleSourceSecondBranchVarianceFloor ε ≤
      saddleSourceGaussianVariance ε ℓ u)
    (hfloorpos : 0 < saddleSourceSecondBranchVarianceFloor ε) :
    saddleSourceSecondBranchCentralRadius ε ℓ u ≤
      (1 / Real.sqrt
        (saddleSourceSecondBranchVarianceFloor ε)) *
          ℓ ^ (-(5 / 12 : ℝ)) := by
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u :=
    hfloorpos.trans_le hfloor
  have hz : 0 ≤ ℓ ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg hℓ.le _
  calc
    saddleSourceSecondBranchCentralRadius ε ℓ u =
        ℓ ^ (1 / 12 : ℝ) /
          Real.sqrt
            (ℓ * saddleSourceGaussianVariance ε ℓ u) := rfl
    _ ≤ ℓ ^ (1 / 12 : ℝ) /
          Real.sqrt
            (ℓ * saddleSourceSecondBranchVarianceFloor ε) := by
      gcongr
    _ = (1 / Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε)) *
        (ℓ ^ (1 / 12 : ℝ) / Real.sqrt ℓ) := by
      rw [Real.sqrt_mul hℓ.le]
      ring
    _ = (1 / Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε)) *
        ℓ ^ (-(5 / 12 : ℝ)) := by
      rw [saddleSource_central_rpow_div_sqrt hℓ]
end CohnElkies
