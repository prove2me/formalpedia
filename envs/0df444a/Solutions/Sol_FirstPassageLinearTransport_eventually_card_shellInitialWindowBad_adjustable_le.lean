-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_card_shellInitialWindowBad_adjustable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:27.337273+00:00
-- url     : https://prove2.me/submissions/39b2e40f-8a73-46bc-880b-e7409c1075b4

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_eventually_adjustableBarrier_startups
import Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_adjustable_le

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      ((shellInitialWindowBad M t).card : ℝ) ≤
        (2 : ℝ) ^ (M + 1) *
          Real.exp (-((M : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  filter_upwards [eventually_adjustableBarrier_startups
    hlambda1 ht0 htA] with M hstartup
  exact card_shellInitialWindowBad_adjustable_le
    hlambda0 hlambda1.le ht0.le htA hstartup.1 hstartup.2
end FirstPassageLinearTransport
