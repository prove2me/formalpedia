-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.hat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:56.057601+00:00
-- url     : https://prove2.me/submissions/6a1e09a7-4bb0-4dfb-9261-b35de5b097d1

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
open Formalism.FourierDecayAlt.P.Qx6.HatData
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
variable {H}
variable (H)
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6.HatData
theorem _root_.solution {T : X → X} (h : H.Good T) (x : H.V) : ((H.hat T x : H.V) : X) = H.N (T x) := by
  unfold HatData.hat
  rw [dif_pos h] <;> rfl
end Formalism.FourierDecayAlt.P.Qx6.HatData
