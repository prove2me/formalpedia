-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.blk_revIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:27.195184+00:00
-- url     : https://prove2.me/submissions/4b1f7a47-52eb-4c62-8451-36fc18a36b5f

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures
namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, blk, hj, if_true, h2]
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, blk, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, solution s (j - a) (by simp at h; omega)]
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
