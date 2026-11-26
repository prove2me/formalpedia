-- Prove2me | solution 1 for FirstPassageLinearTransport.stageCountRpowUpper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:59.989815+00:00
-- url     : https://prove2.me/submissions/83afdbfe-3207-4ba5-afba-ff44933669b2

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
import Theorems.Thm_FirstPassageLinearTransport_rpowLogScheduleIdentity
import Theorems.Thm_FirstPassageLinearTransport_stageCount_gt_sub_one


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r omega : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℕ) :
    r ^ (stageCount omega M) ≤
      r⁻¹ * ((M : ℝ) + 4) ^ (-descentAlpha omega r) := by
  have hx : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hfloor := stageCount_gt_sub_one (omega := omega) M
  have hp : r ^ (stageCount omega M : ℝ) ≤
      r ^ (omega * Real.log ((M : ℝ) + 4) - 1) :=
    (Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 hfloor).le
  rw [Real.rpow_natCast] at hp
  calc
    r ^ stageCount omega M ≤
        r ^ (omega * Real.log ((M : ℝ) + 4) - 1) := hp
    _ = r⁻¹ * ((M : ℝ) + 4) ^ (-descentAlpha omega r) := by
      rw [Real.rpow_sub hr0, Real.rpow_one,
        rpowLogScheduleIdentity hr0 hx]
      unfold descentAlpha densityGamma
      ring
end FirstPassageLinearTransport
