-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.left_derivative_has_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:57.304027+00:00
-- url     : https://prove2.me/submissions/72207e51-08d7-4dd6-8588-8ab6598be557

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_neg_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_curveL
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
    HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g))
      (fderiv ℝ f' g (-(X0 k r * g))) 0 := by
  have hγ := hasDerivAt_curveL (k := k) (r := r) g
  have hγ0 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • X0 k r)) * g = g := by
    simp [NormedSpace.exp_zero]
  have hcomp : HasDerivAt (fun s : ℝ => f' (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g))
      (fderiv ℝ f' g (-(X0 k r * g))) 0 :=
    hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, NormedSpace.exp (-((s : ℂ) • X0 k r)) * g ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with s hs
  exact he _ hs (WeylGroupFacts.uh_mul (exp_neg_mem k r s) hg)
end Formalism.FourierDecayAlt.P.B6
