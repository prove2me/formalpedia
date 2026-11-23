-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LastBlockReversal.blk_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:40.206493+00:00
-- url     : https://prove2.me/submissions/c234ed7a-3dc1-4430-9c7e-f79a64e1cea2

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LastBlockReversal
namespace Formalism.FourierDecayAlt.P.LastBlockReversal
theorem _root_.solution (l : List ℕ) : Formalism.DoubleCosetMeasures.blk (l ++ [1]) l.sum = l.length := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.blk]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, List.length_cons, Formalism.DoubleCosetMeasures.blk]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]
    omega
end Formalism.FourierDecayAlt.P.LastBlockReversal
