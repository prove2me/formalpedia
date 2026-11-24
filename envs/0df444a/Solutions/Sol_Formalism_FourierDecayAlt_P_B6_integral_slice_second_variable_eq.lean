-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.integral_slice_second_variable_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:05:59.064388+00:00
-- url     : https://prove2.me/submissions/6189ad85-8bfa-4b23-8857-b0994643044b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_sum_split

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
theorem _root_.solution {K K' : ℝ → ℝ → ℂ} (x₁ x₂ : ℝ) (c : ℂ)
    (hK : Integrable fun t : ℝ × ℝ => K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (hK' : Integrable fun t : ℝ × ℝ => K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (h : ∀ x, (∫ y, K x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) =
      c * ∫ y, K' x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) :
    (∫ t : ℝ × ℝ, K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      c * ∫ t : ℝ × ℝ, K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
  have key : ∀ (L : ℝ → ℝ → ℂ) (x : ℝ),
      (∫ y, L x y * Complex.exp (Complex.I * ((x₁ * x + x₂ * y : ℝ) : ℂ))) =
        (∫ y, L x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ)) := fun L x => by
    rw [← integral_mul_const]
    congr 1; funext y; rw [exp_sum_split]; ring
  rw [Measure.volume_eq_prod, integral_prod _ hK, integral_prod _ hK', ← integral_const_mul]
  congr 1; funext x
  simp only []
  rw [key K x, key K' x, h x]; ring
end Formalism.FourierDecayAlt.P.B6
