-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.cd_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:33.144996+00:00
-- url     : https://prove2.me/submissions/83e17362-ea46-4b58-80ca-7c1701519ae1

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
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A : X → Mx k r} :
    ContDiffOn ℝ ∞ A s ↔ ∀ p q, ContDiffOn ℝ ∞ (fun x => A x p q) s := by
  refine contDiffOn_pi.trans ?_
  exact forall_congr' fun p => contDiffOn_pi
end Formalism.FourierDecayAlt.P.Qx6
