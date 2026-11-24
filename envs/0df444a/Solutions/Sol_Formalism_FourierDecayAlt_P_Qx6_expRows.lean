-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.expRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:39:54.420297+00:00
-- url     : https://prove2.me/submissions/b7eaaf05-0fe8-45d8-927d-a766857b5a3f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_rowExpFirst
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_rowExpLast
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution : ExpRowsFromRowForm := by
  intro hRF
  refine ⟨?_, ?_⟩
  · intro A _ _ n t E hE a b u
    rw [hRF A n (t + 1) E hE a b u, rowExpFirst E a b u]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hRF A n t E hE (a ∘ Fin.succ) (b ∘ l.succAbove) u]
  · intro A _ _ n t E hE a b u
    rw [hRF A n (t + 1) E hE a b u, rowExpLast E a b u]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hRF A n t E hE (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1)]
end Formalism.FourierDecayAlt.P.Qx6
