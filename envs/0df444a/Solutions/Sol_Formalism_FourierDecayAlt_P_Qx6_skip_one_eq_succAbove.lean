-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.skip_one_eq_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:41:04.08961+00:00
-- url     : https://prove2.me/submissions/0ec4cd9b-a9e7-45a1-94e1-cbe92d34f253

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {t : ℕ} (i : Fin (t + 1)) : (skip1 i : Fin t → Fin (t + 1)) = i.succAbove := by
  funext j
  apply Fin.ext
  simp only [skip1]
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]; exact h)]
    try rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val, Fin.coe_castSucc]; omega)]
    try rfl
end Formalism.FourierDecayAlt.P.Qx6
