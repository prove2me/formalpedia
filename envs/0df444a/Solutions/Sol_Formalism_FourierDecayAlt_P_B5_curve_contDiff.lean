-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.curve_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:59.626148+00:00
-- url     : https://prove2.me/submissions/06e05ec8-be54-4d24-9ca1-38162ef04f54

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt

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
theorem _root_.solution (g X : Mat k r) : ContDiff ℝ 1 (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
  rw [contDiff_one_iff_deriv]
  have hd : Differentiable ℝ (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    fun t => (curve_hasDerivAt g X t).differentiableAt
  refine ⟨hd, ?_⟩
  have hc : Continuous fun t : ℝ => mulRightRealCLM X (g * NormedSpace.exp ((t : ℂ) • X)) :=
    (mulRightRealCLM X).continuous.comp hd.continuous
  exact (continuous_congr fun t => (curve_hasDerivAt g X t).deriv).2 hc
end Formalism.FourierDecayAlt.P.B5
