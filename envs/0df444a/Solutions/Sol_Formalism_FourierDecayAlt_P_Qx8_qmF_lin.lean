-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.qmF_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:22.804801+00:00
-- url     : https://prove2.me/submissions/3d47a451-5080-49f5-991c-4bdfa32da47c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Topology
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] {n t : ℕ} (Eop : Fin n → Fin n → W → W)
    (hE : ∀ a b, IsLin (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : IsLin (qmF Eop a b u) := by
  unfold qmF
  refine IsLin.sum _ fun σ _ => IsLin.smul (IsLin.foldr _ ?_) _
  intro T hT
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  refine IsLin.add ?_ (hE _ _)
  split_ifs
  · exact IsLin.id.smul _
  · exact IsLin.zero
end Formalism.FourierDecayAlt.P.Qx8
