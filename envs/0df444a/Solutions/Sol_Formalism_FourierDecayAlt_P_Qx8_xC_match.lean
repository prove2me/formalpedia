-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.xC_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:00.796702+00:00
-- url     : https://prove2.me/submissions/c0019ec1-f62d-40a8-904f-e622fd832f3e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_second_projection_preserves_ok
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_prod_match
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_rho_anti
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
theorem _root_.solution (h : P.OK) (σ : Ty (P1 P)) (τ : Ty (P2 P)) (he : ∀ Y, xC (P1 P) σ Y = xC (P2 P) τ Y) :
    ∃ ρ : Ty P, ∀ Y, xC P ρ Y = xC (P1 P) σ Y := by
  have hm : ∀ j ∈ Finset.Icc 1 (P.k - 1), rho (P1 P) σ j = rho (P2 P) τ j :=
    prod_match _ _ _ (rho_anti (first_projection_preserves_ok h) σ) (rho_anti (second_projection_preserves_ok h) τ) he
  have h1 := types_interlace (P1 P) (first_projection_preserves_ok h) σ
  have h2 := types_interlace (P2 P) (second_projection_preserves_ok h) τ
  obtain ⟨n₁, hn₁⟩ := h.int_u' 1 (one_mem_Icc h)
  obtain ⟨ρ, hρ⟩ := (types_complete P h).1 (rho (P1 P) σ)
    (fun i hi => ⟨by rw [hm i hi]; exact (h2 i hi).1, (h1 i hi).1, by rw [hm i hi]; exact (h2 i hi).2.2.1,
      (h1 i hi).2.2.1⟩)
    (fun i hi => by
      obtain ⟨n, hn⟩ := rho_int (first_projection_preserves_ok h) σ i hi
      have hn' : rho (P1 P) σ i - P.u' 1 - 1 / 2 = n := hn
      exact ⟨n + n₁, by push_cast; linarith⟩)
  refine ⟨ρ, fun Y => ?_⟩
  unfold xC
  exact Finset.prod_congr rfl fun i hi => by rw [hρ i hi]
end Formalism.FourierDecayAlt.P.Qx8
