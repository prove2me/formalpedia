-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:09.836666+00:00
-- url     : https://prove2.me/submissions/5a7afd1c-94c7-4711-97ac-426dfa275cad

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_lint_KM_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_enorm_om_le

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ p, D.inSS p → (∫⁻ x, ‖Om D w₁ w₂ p * KM D F p x‖ₑ ∂D.μG) ≤
      K * (u_fX D.z Ξ p.1 * u_fX D.z' Ξ p.2) := by
  obtain ⟨K0, hK0, h0⟩ := u_lint_KM_le D Ξ A hCB hF
  obtain ⟨K1, hK1, e1⟩ := u_enorm_om_le h₁
  obtain ⟨K2, hK2, e2⟩ := u_enorm_om_le h₂
  refine ⟨K1 * K2 * K0, ENNReal.mul_ne_top (ENNReal.mul_ne_top hK1 hK2) hK0, fun p hp => ?_⟩
  simp only [enorm_mul]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  have a1 := e1 (lam k r D.z (Matrix.of p.1.2))
  have a2 := e2 (-lam k r D.z' (Matrix.of p.2.2))
  rw [abs_neg] at a2
  have a0 := h0 p hp
  have aO : ‖Om D w₁ w₂ p‖ₑ ≤ (K1 * ENNReal.ofReal ((1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-(2 : ℝ)))) *
      (K2 * ENNReal.ofReal ((1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-(2 : ℝ)))) := by
    unfold Om
    rw [enorm_mul]
    exact mul_le_mul' a1 a2
  refine (mul_le_mul' aO a0).trans (le_of_eq ?_)
  unfold u_fX
  ring
end Formalism.FourierDecayAlt.P.B7
