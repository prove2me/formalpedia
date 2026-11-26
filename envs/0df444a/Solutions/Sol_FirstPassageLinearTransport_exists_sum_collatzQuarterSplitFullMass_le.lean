-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:10.396034+00:00
-- url     : https://prove2.me/submissions/2772996e-7027-4f5f-b387-c9670ec2656f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzFullThreeBlockMass_le_envelope
import Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFairBinMass_le

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzFullThreeBlockMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C, hC, hEnvelope⟩ :=
    exists_sum_collatzQuarterSplitFairBinMass_le
  refine ⟨C, hC, ?_⟩
  intro m Q B hm hB
  calc
    (∑ q ∈ Finset.range Q,
        collatzFullThreeBlockMass (1 / 2)
          (collatzBallotOuterLength m)
          (collatzBallotMiddleLength m) B q) ≤
        ∑ q ∈ Finset.range Q,
          collatzThreeBlockFlatMass (1 / 2)
            (collatzBallotOuterLength m)
            (collatzBallotMiddleLength m) B q := by
      apply Finset.sum_le_sum
      intro q _hq
      exact collatzFullThreeBlockMass_le_envelope _ _ _ _
    _ ≤ C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hEnvelope m Q B hm hB
end FirstPassageLinearTransport
