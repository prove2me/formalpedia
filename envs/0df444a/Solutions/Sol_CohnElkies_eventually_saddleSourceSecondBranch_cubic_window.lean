-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_cubic_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/d1cb7e50-b74f-4973-a7db-20c95bea6c86

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_cubic_central_window_le

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
            ∀ T : ℝ,
              |T| ≤
                saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
              (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
                  |T| ^ 3 < κ := by
  filter_upwards [
    eventually_saddleSourceSecondBranch_cubic_central_window_le]
    with ε hquant
  intro κ hκ
  let A : ℝ :=
    (2 + (100 / 99 : ℝ) *
      upperSaddleShellThirdCoefficient ε) /
        (6 * Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε))
  have htendsto :
      Tendsto (fun ℓ : ℝ => A * ℓ ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 1 / 4)) using 1
    all_goals simp
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    htendsto.eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hsmall
  intro δ hδ T hT
  exact (hquant ℓ hℓ δ hδ T hT).trans_lt hsmall
end CohnElkies
