-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Bt_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:25.466255+00:00
-- url     : https://prove2.me/submissions/ac6c91c4-2e72-42d2-95ae-60f007b73c6b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regBracket_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_pairing_continuous_in_t
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_mul_of_vanishing_outside_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_square_product_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_square_product_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun t : ℝ × ℝ => Bt D F F' (p, t)) := by
  by_cases hp : D.inSS p
  · have e : (fun t : ℝ × ℝ => Bt D F F' (p, t)) =
        fun t => ((Wd D t.1 * Wd D t.2 : ℝ) : ℂ) * QR D p 0 0 F F' t.1 t.2 :=
      funext fun t => (Bt_eq D F F' hp t).trans (regBracket_eq D F F' p t.1 t.2)
    rw [e]
    refine continuous_mul_of_vanishing_outside_box (cutoff_square_product_continuous D) (fun t ht => ?_)
      (regularised_pairing_continuous_in_t H (admissibleWeight_mono hF (by omega) (by omega)) (admissibleWeight_mono hF' (by omega) (by omega)) hp)
    rw [cutoff_square_product_zero D ht]; simp
  · have e : (fun t : ℝ × ℝ => Bt D F F' (p, t)) = fun _ => 0 := funext (Bt_zero' D F F' hp)
    rw [e]
    exact continuous_const
end Formalism.FourierDecayAlt.P.B6
