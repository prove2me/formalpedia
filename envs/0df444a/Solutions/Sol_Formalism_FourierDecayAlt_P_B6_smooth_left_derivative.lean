-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.smooth_left_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:01.628774+00:00
-- url     : https://prove2.me/submissions/4b6dbdcb-d523-42e4-a4af-954fceb3fa4a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_contDiff_matrix_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_left_derivative_has_deriv

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
theorem _root_.solution {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) :
    CkOn (n : ℕ∞) (GV k r) (Ll f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (-(X0 k r * g)), hU, hgU, ?_, ?_⟩
  · exact ContDiffOn.clm_apply (hf'.fderiv_of_isOpen hU (m := ((n : ℕ∞) : WithTop ℕ∞)) (by norm_cast))
      (contDiff_matrix_mul_left (X0 k r)).neg.contDiffOn
  · intro g hgU' hg
    have hd : DifferentiableAt ℝ f' g :=
      (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU')
    exact (left_derivative_has_deriv hU hgU' hg hd he).deriv
end Formalism.FourierDecayAlt.P.B6
