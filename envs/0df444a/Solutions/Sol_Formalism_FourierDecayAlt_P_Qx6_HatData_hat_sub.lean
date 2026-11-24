-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.hat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:14.163927+00:00
-- url     : https://prove2.me/submissions/dfa79c6f-c1f9-4c25-8609-97e0fcbed24e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_apply

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
theorem _root_.solution {T S : X → X} (hT : H.Good T) (hS : H.Good S) :
    H.hat (fun x => T x - S x) = H.hat T - H.hat S := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => T x - S x) x : H.V) : X) = ((H.hat T x : H.V) : X) - ((H.hat S x : H.V) : X)
  rw [hat_apply (hT.sub hS), hat_apply hT, hat_apply hS]
  exact map_sub H.N _ _
end Formalism.FourierDecayAlt.P.Qx6.HatData
