-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.fourier_transform_quadratic_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:40:46.642702+00:00
-- url     : https://prove2.me/submissions/14b0b0be-4de1-4652-8a60-0df06a1aef19

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rpow_neg_two_eq_inv_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_test_function_decay


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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {w : ℝ → ℝ} (hw : IsTest w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖om w x‖ ≤ C * (1 + |x|) ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.test_function_decay w hw
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [rpow_neg_two_eq_inv_sq (by positivity)]
  exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
end Formalism.FourierDecayAlt.P.B6
