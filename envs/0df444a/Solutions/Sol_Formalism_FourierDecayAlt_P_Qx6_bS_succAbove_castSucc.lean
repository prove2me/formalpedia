-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bS_succAbove_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:43.019033+00:00
-- url     : https://prove2.me/submissions/05c09e31-9ecd-4700-a9bc-cda1bf554c22

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
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {m : ℕ} (e : Fin n) (v : Fin (m + 1) → Fin n) (w : Fin (m + 1)) :
    bS v e ∘ w.castSucc.succAbove = bS (v ∘ w.succAbove) e := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Function.comp_apply, Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)), Fin.succ_last]
    simp [bS]
  | cast k => simp [bS, Fin.castSucc_succAbove_castSucc]
end Formalism.FourierDecayAlt.P.Qx6
