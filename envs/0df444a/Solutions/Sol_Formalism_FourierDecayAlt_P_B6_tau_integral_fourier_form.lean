-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.tau_integral_fourier_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:11:24.952215+00:00
-- url     : https://prove2.me/submissions/18fe0bad-ac0f-4a56-84d8-00f161abe85b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integrable_test_weighted_phase_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_test_product_tau_fourier_integral

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
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p : SS k r) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Gt D F F' τ p) =
      ∫ t : ℝ × ℝ, Bt D F F' (p, t) *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))) := by
  simp_rw [Gt_eq H hF hF', ← integral_const_mul]
  rw [integral_integral_swap (integrable_test_weighted_phase_product H hF hF' h₁ h₂ p)]
  congr 1
  funext t
  rw [← test_product_tau_fourier_integral, ← integral_const_mul]
  congr 1
  funext τ
  have : phase D τ p t = τ.1 * (t.1 * lam k r D.z (Matrix.of p.1.2)) -
      τ.2 * (t.2 * lam k r D.z' (Matrix.of p.2.2)) := by
    unfold phase; ring
  rw [this]
  ring
end Formalism.FourierDecayAlt.P.B6
