-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.oneMinusDD_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:53:56.73354+00:00
-- url     : https://prove2.me/submissions/07db15a3-f676-47f4-860f-286824b85299

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
theorem _root_.solution (a : ℂ) (h : ℝ → ℝ → ℂ) (x y : ℝ) :
    oneMinusDD (fun x y => a * h x y) x y = a * oneMinusDD h x y := by
  have i2 : (fun x => a * h x y - iteratedDeriv 2 (fun y' => a * h x y') y) =
      fun x => a * (h x y - iteratedDeriv 2 (fun y' => h x y') y) := by
    funext x; rw [iteratedDeriv_const_mul_field]; ring
  unfold oneMinusDD
  simp only []
  rw [i2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  ring
end Formalism.FourierDecayAlt.P.B6
