-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellInitialWindowBad_adjustable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:18.201798+00:00
-- url     : https://prove2.me/submissions/f6617432-45b3-4638-99de-8d1dfe847a8d

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_shellInitialWindowBad_subset_adjustable
import Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_adjustable_le

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M : ℕ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have hsubset := shellInitialWindowBad_subset_adjustable
    hlambda1 ht0 hmainStartup hcorrectionStartup
  have hcard :
      (shellInitialWindowBad M t).card ≤
        (shellMaximalParityBad M
          (adjustableBarrierHeight lambda t M)).card :=
    Finset.card_le_card hsubset
  have hcardR :
      ((shellInitialWindowBad M t).card : ℝ) ≤
        ((shellMaximalParityBad M
          (adjustableBarrierHeight lambda t M)).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (card_shellMaximalParityBad_adjustable_le M hlambda0 hlambda1 ht0 htA)
end FirstPassageLinearTransport
