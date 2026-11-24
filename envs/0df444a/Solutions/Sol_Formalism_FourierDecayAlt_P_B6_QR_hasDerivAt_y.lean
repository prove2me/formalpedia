-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.QR_hasDerivAt_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:47:06.857959+00:00
-- url     : https://prove2.me/submissions/4ae0aeac-dc14-419a-bcd8-08dc4b08d8ba

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_hasDerivAt_y

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
theorem _root_.solution (H : Hyp D Ξ α) {l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA (l + 1) 0 A) (hB : AdmW α cB (l + 1) 0 B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => QR D p 0 l A B x y') (((-(rr r / y) : ℝ) : ℂ) * QR D p 0 (l + 1) A B x y) y := by
  induction l generalizing A B with
  | zero =>
    exact ph_hasDerivAt_y H (hA.1 0 (by omega) 0 le_rfl) (hA.1 1 le_rfl 0 le_rfl) (hB.1 0 (by omega) 0 le_rfl)
      (hB.1 1 le_rfl 0 le_rfl) (hA.2.1 0 (by omega)) (hB.2.1 0 (by omega)) hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3
end Formalism.FourierDecayAlt.P.B6
