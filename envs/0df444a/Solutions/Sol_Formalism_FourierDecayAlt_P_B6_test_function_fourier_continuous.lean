-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.test_function_fourier_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:19.648471+00:00
-- url     : https://prove2.me/submissions/9a79b385-3761-4dee-8051-ee68e944f5e6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_exp_I_mul_ofReal_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_test_function_integrable

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
theorem _root_.solution {w : ℝ → ℝ} (hw : IsTest w) : Continuous (om w) := by
  unfold om
  refine continuous_of_dominated (bound := fun τ => ‖w τ‖) ?_ ?_ (test_function_integrable hw).norm ?_
  · intro x
    have hc : Continuous fun τ : ℝ => (w τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ)) := by
      have := hw.1.continuous
      fun_prop
    exact hc.aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun τ => ?_
    rw [norm_mul, norm_exp_I_mul_ofReal_eq_one, mul_one, Complex.norm_real]
  · refine Filter.Eventually.of_forall fun τ => ?_
    fun_prop
end Formalism.FourierDecayAlt.P.B6
