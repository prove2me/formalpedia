-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.hat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:17.497596+00:00
-- url     : https://prove2.me/submissions/e283172d-79da-4f2e-b806-68f68ba47068

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


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
theorem _root_.solution {T : X → X} (hT : H.Good T) (a : ℂ) : H.hat (fun x => a • T x) = a • H.hat T := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => a • T x) x : H.V) : X) = a • ((H.hat T x : H.V) : X)
  rw [hat_apply (hT.smul a), hat_apply hT]
  exact map_smul H.N a _
end Formalism.FourierDecayAlt.P.Qx6.HatData
