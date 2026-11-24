-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.good_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:58.709508+00:00
-- url     : https://prove2.me/submissions/6efefa6a-79f6-4d40-a48f-e6b3a3a85c9d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
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
theorem _root_.solution : H.Good (fun _ => (0 : X)) where
  mem := fun _ _ => H.G.zero_mem
  congr := fun _ _ _ _ _ => rfl
  lin := fun _ _ _ _ _ => by simp
end Formalism.FourierDecayAlt.P.Qx6.HatData
