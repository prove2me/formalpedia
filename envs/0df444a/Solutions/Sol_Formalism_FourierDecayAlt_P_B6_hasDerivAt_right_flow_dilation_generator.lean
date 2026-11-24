-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hasDerivAt_right_flow_dilation_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:28.027161+00:00
-- url     : https://prove2.me/submissions/fbf099fd-9b83-4cd4-8a3f-6dee59759fc8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_curveR
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_exp_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hf' : DifferentiableAt ℝ f' g) (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X0 k r))) (fderiv ℝ f' g (g * X0 k r)) 0 := by
  have hγ := hasDerivAt_curveR (k := k) (r := r) g
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X0 k r) = g := by
    simp [NormedSpace.exp_zero]
  have hcomp : HasDerivAt (fun s : ℝ => f' (g * NormedSpace.exp ((s : ℂ) • X0 k r)))
      (fderiv ℝ f' g (g * X0 k r)) 0 :=
    hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, g * NormedSpace.exp ((s : ℂ) • X0 k r) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with s hs
  exact he _ hs (WeylGroupFacts.uh_mul hg (exp_mem k r s))
end Formalism.FourierDecayAlt.P.B6
