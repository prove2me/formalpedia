-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.cd_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:51.238492+00:00
-- url     : https://prove2.me/submissions/b0e46d90-5365-456e-a630-cec90c159c3c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coord


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
theorem _root_.solution (l : Fin r) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => ((‖c l‖ ^ n : ℝ) : ℂ)) (OmX r) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (((Qx3.cd_coord l).contDiffOn.norm ℝ (fun x (hx : x ∈ OmX r) => hx l)).pow n)
end Formalism.FourierDecayAlt.P.Qx6
