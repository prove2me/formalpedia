-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_bracket_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:41.055084+00:00
-- url     : https://prove2.me/submissions/fe166f69-4b0d-496f-b5b8-669c0fb44996

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_al2
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_QR_hasDerivAt_y
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_pairing_deriv_x
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regBracket_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_pairing_continuous_in_t

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
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) :
    (∀ x y, oneMinusDD (regBracket D F F' p) x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam (rr r) (Wd D) m x * gam (rr r) (Wd D) l y : ℝ) : ℂ) * QR D p m l F F' x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => regBracket D F F' p x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => regBracket D F F' p x y -
      iteratedDeriv 2 (fun y' => regBracket D F F' p x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) :=
  al2 (Wd_contDiff D) (Wd_tsupport D) (rr r) (fun m l x y => QR D p m l F F' x y)
    (fun l hl x hx y hy => QR_hasDerivAt_y H (admissibleWeight_mono hF (by omega) (by omega))
      (admissibleWeight_mono hF' (by omega) (by omega)) hp hx hy)
    (fun m hm l hl x hx y hy => regularised_pairing_deriv_x H (admissibleWeight_mono hF hl (by omega))
      (admissibleWeight_mono hF' hl (by omega)) hp hx hy)
    (fun m hm l hl => regularised_pairing_continuous_in_t H (admissibleWeight_mono hF hl hm) (admissibleWeight_mono hF' hl hm) hp)
    (regBracket D F F' p) (regBracket_eq D F F' p)
end Formalism.FourierDecayAlt.P.B6
