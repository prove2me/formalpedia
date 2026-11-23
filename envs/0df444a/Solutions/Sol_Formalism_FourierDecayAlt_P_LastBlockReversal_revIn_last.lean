-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LastBlockReversal.revIn_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:55.734791+00:00
-- url     : https://prove2.me/submissions/ebde125b-caf4-4612-a712-33882cef84b7

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
theorem _root_.solution (l : List ℕ) : Formalism.DoubleCosetMeasures.revIn (l ++ [1]) l.sum = l.sum := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.revIn]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, Formalism.DoubleCosetMeasures.revIn]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]
end Formalism.FourierDecayAlt.P.LastBlockReversal
