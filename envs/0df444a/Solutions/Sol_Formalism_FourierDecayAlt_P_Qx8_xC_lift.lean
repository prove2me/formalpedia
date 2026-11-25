-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.xC_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:59.333329+00:00
-- url     : https://prove2.me/submissions/163fb314-241f-4bf4-a33a-75f584b393f4

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_one_mem_Icc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_first_projection_preserves_ok
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_rho_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_types_complete
import Theorems.Thm_Formalism_FourierDecayAlt_P_types_interlace


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
open Formalism.FourierDecayAlt.M
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (h : P.OK) (ρ : Ty P) : ∃ σ : Ty (P1 P), ∀ Y, xC (P1 P) σ Y = xC P ρ Y := by
  have hI := types_interlace P h ρ
  obtain ⟨n₁, hn₁⟩ := h.int_u' 1 (one_mem_Icc h)
  obtain ⟨σ, hσ⟩ := (types_complete (P1 P) (first_projection_preserves_ok h)).1 (rho P ρ)
    (fun i hi => ⟨(hI i hi).2.1, (hI i hi).2.1, (hI i hi).2.2.2, (hI i hi).2.2.2⟩)
    (fun i hi => by
      obtain ⟨n, hn⟩ := rho_int h ρ i hi
      refine ⟨n - n₁, ?_⟩
      show rho P ρ i - P.u' 1 - 1 / 2 = _
      push_cast; linarith)
  refine ⟨σ, fun Y => ?_⟩
  unfold xC
  exact Finset.prod_congr rfl fun i hi => by rw [hσ i hi]
end Formalism.FourierDecayAlt.P.Qx8
