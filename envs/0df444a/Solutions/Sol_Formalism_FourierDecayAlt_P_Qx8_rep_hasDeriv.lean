-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.rep_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:23:52.483034+00:00
-- url     : https://prove2.me/submissions/83516dff-379a-4d5e-91b4-2d6e2db01a03

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_lcurve_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_oneParam_diff
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f


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
variable {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {U : Set (Mx k r)} {π : Mx k r → (Wp →L[ℂ] Wp)} (hrep : IsCRepOn U π)
    (hcont : ContinuousOn π U) {X : Mx k r} (hX : InU U X) (v : Wp) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dRep π X v) 0 := by
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hce : Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    have := lcurve_cont X (1 : Mx k r)
    simpa only [Matrix.mul_one] using this
  have hφ := oneParam_diff (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)))
    (hcont.comp_continuous hce hX) (by simp [NormedSpace.exp_zero, hrep.1])
    (fun s t => by
      have e := B5.exp_add' X s t
      push_cast at e
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      push_cast
      rw [e, hrep.2 _ (hX s) _ (hX t)]
      rfl)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) 0 :=
    ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).differentiableAt.comp 0 hφ
  exact hd.hasDerivAt
end Formalism.FourierDecayAlt.P.Qx8
