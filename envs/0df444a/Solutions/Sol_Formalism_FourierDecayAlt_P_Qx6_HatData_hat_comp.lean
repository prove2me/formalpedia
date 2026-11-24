-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.hat_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:59:19.892662+00:00
-- url     : https://prove2.me/submissions/b38e22a6-77cf-4a14-a0bb-26a39738a96c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
    H.hat (fun x => T (S x)) = H.hat T * H.hat S := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => T (S x)) x : H.V) : X) = ((H.hat T (H.hat S x) : H.V) : X)
  rw [hat_apply (hT.comp hS), hat_apply hT, hat_apply hS]
  exact hT.congr _ (hS.mem _ x.2.1) _ (H.N_mem _ (hS.mem _ x.2.1)) (H.N_idem _).symm
end Formalism.FourierDecayAlt.P.Qx6.HatData
