-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.nf_low_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:54.664077+00:00
-- url     : https://prove2.me/submissions/c501a9fb-5793-41a0-b160-4f2a71be8eb6

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_rho_raise


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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R
variable {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (d : NFData P 𝒜) (hR : d.Rel) (Y : ℂ) (hY : ∀ π, xC P π Y ≠ 0) :
    d.x Y * ∑ j ∈ Icc 1 (P.k - 1), (d.κ fun π => (Y + (rho P π j : ℂ))⁻¹) * d.SS j = d.weightedSumBis Y := by
  rw [Finset.mul_sum, NFData.weightedSumBis]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, NFData.x, ← map_mul]
  refine hR.2.2.2.1 j _ _ fun π π' hU => ?_
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) := Finset.singleton_subset_iff.2 hj
  have h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ)) := by
    rw [xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]
  have h2 : Y + (rho P π' j : ℂ) ≠ 0 := fun h0 => hY π' (by rw [h1, h0, mul_zero])
  have h3 : xEx P {j} π' Y = xEx P {j} π Y := by
    unfold xEx
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    rw [rho_raise P j π π' hU i hi.1, if_neg hi.2, add_zero]
  show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y
  rw [h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]
end Formalism.FourierDecayAlt.P.Qx8
