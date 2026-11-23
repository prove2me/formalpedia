-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.revIn_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:27.578026+00:00
-- url     : https://prove2.me/submissions/2c1098f4-1ad1-4b51-86d4-492cbaa578ed

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
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [revIn]
    split_ifs with hj
    · simp; omega
    · have := solution s (j - a) (by simp at h; omega)
      simp; omega
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
