-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:59:58.425248+00:00
-- url     : https://prove2.me/submissions/a36f9185-0037-4840-aa3b-cd38e399d5ea

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
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
theorem _root_.solution {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r}
    (hg : g ∈ U) (hgG : g ∈ GV k r) (hX : inLie k r X) (hf' : DifferentiableAt ℝ f' g)
    (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ f' g (g * X)) 0 := by
  have hc := curve_hasDerivAt g X 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hc
  have hf'' : HasFDerivAt f' (fderiv ℝ f' g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [curve_zero]
    exact hf'.hasFDerivAt
  have hcomp := hf''.comp_hasDerivAt (0 : ℝ) hc
  apply hcomp.congr_of_eventuallyEq
  have hU' : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hU'] with t ht
  exact he _ ht (curve_mem hgG hX t)
end Formalism.FourierDecayAlt.P.B5
