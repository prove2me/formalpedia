-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.filter_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:48.358373+00:00
-- url     : https://prove2.me/submissions/4b19fabd-5aa9-400a-97de-b6f6533c6e88

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution : ∀ {r : ℕ} (l : Fin r),
    (List.finRange r).filter (fun a => decide (a.val < l.val + 1)) =
      (List.finRange r).filter (fun a => decide (a.val < l.val)) ++ [l]
  | 0, l => l.elim0
  | r + 1, l => by
    rw [List.finRange_succ]
    simp only [List.filter_cons, List.filter_map]
    refine Fin.cases ?_ (fun l' => ?_) l
    · simp [Function.comp_def]
    · have ih := solution l'
      simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, decide_true, if_true, Function.comp_def,
        Nat.add_lt_add_iff_right, List.cons_append]
      rw [ih]
      simp
end Formalism.FourierDecayAlt.P.Qx6
