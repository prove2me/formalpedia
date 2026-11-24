-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.right_derivative_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:18.080115+00:00
-- url     : https://prove2.me/submissions/5fedaf96-0af0-4537-be8f-ad413f10012d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_right_flow_dilation_generator

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
theorem _root_.solution {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) : DR f := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU)
  have h1 := hasDerivAt_right_flow_dilation_generator hU hgU hg hd he
  have h2 : RdV (X0 k r) f g = fderiv ℝ f' g (g * X0 k r) := h1.deriv
  rw [h2]; exact h1
end Formalism.FourierDecayAlt.P.B6
