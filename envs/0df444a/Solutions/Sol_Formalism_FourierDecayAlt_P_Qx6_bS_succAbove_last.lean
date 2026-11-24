-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bS_succAbove_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:52.558096+00:00
-- url     : https://prove2.me/submissions/6e94ba70-5865-4fb7-bdaf-7556c5d9ff0c

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
theorem _root_.solution {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e ∘ (Fin.last m).succAbove = v := by
  funext j
  simp [bS, Fin.succAbove_last]
end Formalism.FourierDecayAlt.P.Qx6
