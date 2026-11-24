-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_pairing_deriv_x
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:28.026674+00:00
-- url     : https://prove2.me/submissions/56905acd-3910-40d1-bb8b-8f74b91a9c8c

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_left_derivative_pairing_x

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
    (hA : AdmW α cA l (m + 1) A) (hB : AdmW α cB l (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QR D p m l A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QR D p (m + 1) l A B x y) x := by
  induction l generalizing A B with
  | zero => exact hasDerivAt_left_derivative_pairing_x H hA hB hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3
end Formalism.FourierDecayAlt.P.B6
