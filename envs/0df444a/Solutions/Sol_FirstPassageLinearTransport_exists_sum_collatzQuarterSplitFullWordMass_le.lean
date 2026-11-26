-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullWordMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:57.164693+00:00
-- url     : https://prove2.me/submissions/a4ba911b-fd7f-4073-806e-8eb19444e424

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzFullWordMass_eq_threeBlock
import Theorems.Thm_FirstPassageLinearTransport_collatzBallot_split
import Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFullMass_le

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
              collatzFullWordMass (1 / 2) m B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C, hC, hThreeBlock⟩ :=
    exists_sum_collatzQuarterSplitFullMass_le
  refine ⟨C, hC, ?_⟩
  intro m Q B hm hB
  have hlen : collatzBallotOuterLength m +
      (collatzBallotMiddleLength m + collatzBallotOuterLength m) = m := by
    have hsplit := collatzBallot_split m
    omega
  calc
    (∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B q) =
        ∑ q ∈ Finset.range Q,
          collatzFullThreeBlockMass (1 / 2)
            (collatzBallotOuterLength m)
            (collatzBallotMiddleLength m) B q := by
      apply Finset.sum_congr rfl
      intro q _hq
      calc
        collatzFullWordMass (1 / 2) m B q =
            collatzFullWordMass (1 / 2)
              (collatzBallotOuterLength m +
                (collatzBallotMiddleLength m +
                  collatzBallotOuterLength m)) B q := by rw [hlen]
        _ = collatzFullThreeBlockMass (1 / 2)
              (collatzBallotOuterLength m)
              (collatzBallotMiddleLength m) B q :=
          collatzFullWordMass_eq_threeBlock _ _ _ _ _
    _ ≤ C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hThreeBlock m Q B hm hB
end FirstPassageLinearTransport
