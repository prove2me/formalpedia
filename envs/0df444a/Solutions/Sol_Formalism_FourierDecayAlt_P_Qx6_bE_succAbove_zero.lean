-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bE_succAbove_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:57.785555+00:00
-- url     : https://prove2.me/submissions/07adf878-7f9f-47ee-a375-f59a13ca2b21

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
theorem _root_.solution {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v ∘ (0 : Fin (m + 1)).succAbove = v := by
  funext j
  simp [bE, Fin.succAbove_zero]
end Formalism.FourierDecayAlt.P.Qx6
