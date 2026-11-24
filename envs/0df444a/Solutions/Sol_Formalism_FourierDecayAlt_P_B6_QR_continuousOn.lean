-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.QR_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:44:57.473801+00:00
-- url     : https://prove2.me/submissions/f4d4d830-3e7a-4884-9895-5ad42c16c60b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_right_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weight_lower_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_quadrant_function_continuous_on

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l m A) (hB : AdmW α cB l m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QR D q.1 m l A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction l generalizing A B with
  | zero => exact quadrant_function_continuous_on H hA hB
  | succ l ih => exact (ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)).add (ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB))
end Formalism.FourierDecayAlt.P.B6
