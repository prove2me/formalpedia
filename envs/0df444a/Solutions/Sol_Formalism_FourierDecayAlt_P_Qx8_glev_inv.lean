-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.glev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:09.210931+00:00
-- url     : https://prove2.me/submissions/a39ccaf0-6e97-4337-893a-43d5f5682a68

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_inv_mul_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  refine ⟨WeylGroupFacts.uh_inv hg.1, fun a ha => ⟨?_, ?_⟩⟩
  · conv_lhs => rw [← (hg.2 a ha).1]
    rw [Matrix.mulVec_mulVec, inv_mul_uh hg.1, Matrix.one_mulVec]
  · conv_lhs => rw [← (hg.2 a ha).2]
    rw [Matrix.mulVec_mulVec, inv_mul_uh hg.1, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.Qx8
