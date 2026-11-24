-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:39:26.907108+00:00
-- url     : https://prove2.me/submissions/c7856b7b-854d-49da-b2f0-f61a5cfd1b60

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (g X : Mat k r) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * NormedSpace.exp ((t₀ : ℂ) • X) * X) t₀ := by
  have h := hasDerivAt_mul_exp_smul_zero (g * NormedSpace.exp ((t₀ : ℂ) • X)) X
  rw [← sub_self t₀] at h
  have h2 := HasDerivAt.comp_sub_const t₀ t₀ h
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show g * NormedSpace.exp ((t : ℂ) • X) =
    g * NormedSpace.exp ((t₀ : ℂ) • X) * NormedSpace.exp (((t - t₀ : ℝ) : ℂ) • X)
  have e : t₀ + (t - t₀) = t := by ring
  rw [Matrix.mul_assoc, ← exp_add', e]
end Formalism.FourierDecayAlt.P.B5
