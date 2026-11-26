-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_interval_card_landingBad_adjustable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:18.615961+00:00
-- url     : https://prove2.me/submissions/12515256-26d3-49a6-b275-aebe42a5f00e

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Theorems.Thm_FirstPassageLinearTransport_eventually_card_landingBad_adjustable_le


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have htail := eventually_card_landingBad_adjustable_le
    hlambda0 hlambda1 ht0 htA
  rw [Filter.eventually_atTop] at htail ⊢
  obtain ⟨q0, hq0⟩ := htail
  refine ⟨q0, ?_⟩
  intro L hL U q hq
  exact hq0 q (hL.trans (Finset.mem_Icc.mp hq).1)
end FirstPassageLinearTransport
