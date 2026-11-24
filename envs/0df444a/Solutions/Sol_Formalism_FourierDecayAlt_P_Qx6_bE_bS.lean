-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bE_bS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:19.4858+00:00
-- url     : https://prove2.me/submissions/751b3308-29d2-427b-adf4-d4d565d55eba

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
theorem _root_.solution {m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : bE e (bS v es) = bS (bE e v) es := by
  simp only [bE, bS]
  exact Fin.cons_snoc_eq_snoc_cons _ _ _
end Formalism.FourierDecayAlt.P.Qx6
