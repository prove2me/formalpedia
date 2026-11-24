-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hasDerivAt_left_derivative_pairing_x
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:20.731928+00:00
-- url     : https://prove2.me/submissions/bcb8002d-0d34-42eb-8c0d-97b409c00cc9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_left_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_of_succ_left_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_dilation_deriv_x

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
theorem _root_.solution (H : Hyp D Ξ α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 (m + 1) A) (hB : AdmW α cB 0 (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QL D p m A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QL D p (m + 1) A B x y) x := by
  induction m generalizing A B with
  | zero =>
    exact phase_dilation_deriv_x H (hA.1 0 le_rfl 0 (by omega)) (hA.1 0 le_rfl 1 le_rfl) (hB.1 0 le_rfl 0 (by omega))
      (hB.1 0 le_rfl 1 le_rfl) (hA.2.2 0 le_rfl 0 (by omega)) (hB.2.2 0 le_rfl 0 (by omega)) hp hx hy
  | succ m ih =>
    have h1 := ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)
    have h2 := ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3
end Formalism.FourierDecayAlt.P.B6
