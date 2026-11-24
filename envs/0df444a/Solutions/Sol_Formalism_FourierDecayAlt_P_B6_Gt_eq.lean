-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Gt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:54.778846+00:00
-- url     : https://prove2.me/submissions/84e30b4f-757d-4103-b973-b216574b61d6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_E_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_E_ibp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110
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
    (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) (p : SS k r) :
    Gt D F F' τ p = ∫ t : ℝ × ℝ, Bt D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ)) := by
  by_cases hp : D.inSS p
  · unfold Gt
    have e1 : (∫ t : ℝ × ℝ, Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) =
        ∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 * Complex.exp (Complex.I *
          ((τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 : ℝ) : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only []
      rw [Et_eq D F F' hp, E_formula H hF hF' hp]
      have : phase D τ p t =
          τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := by
        unfold phase; ring
      rw [this]
    have e2 : (∫ t : ℝ × ℝ, Bt D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) =
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 * Complex.exp (Complex.I *
          ((τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 : ℝ) : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only []
      rw [Bt_eq D F F' hp]
      have : phase D τ p t =
          τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := by
        unfold phase; ring
      rw [this]
    rw [e1, e2, E_ibp H hF hF' hp, ← mul_assoc, ← Complex.ofReal_mul]
    have : wt D τ p * ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
      unfold wt
      have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
      have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
      field_simp
    rw [this]
    simp
  · simp [Gt, Et_zero' D F F' hp, Bt_zero' D F F' hp]
end Formalism.FourierDecayAlt.P.B6
