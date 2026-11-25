-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.integrable_OmK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:30.001891+00:00
-- url     : https://prove2.me/submissions/7a4034d5-c0f2-4428-a1f7-7df546cb44f9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_contOn_of_CkOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_meas_fX
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_inner_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_sm_OmK

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
    (hXi : XiInt D Ξ 2) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) :
    Integrable (fun a : SS k r × Mt k r => Om D w₁ w₂ a.1 * KM D F a.1 a.2) (D.μSS.prod D.μG) := by
  have hcont : ContinuousOn F (GV k r) := by
    obtain ⟨c, hc1, _⟩ := hF
    exact contOn_of_CkOn hc1
  have hsm := u_sm_OmK D hcont h₁ h₂
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hsm.enorm.aemeasurable]
  obtain ⟨K, hK, hle⟩ := u_inner_le D Ξ A hCB hF h₁ h₂
  have m1 := (u_meas_fX D.z hXi.1).aemeasurable (μ := D.μW.prod D.μN)
  have m2 := (u_meas_fX D.z' hXi.1).aemeasurable (μ := D.μW'.prod D.μN)
  have f1 : (∫⁻ p, u_fX D.z Ξ p ∂(D.μW.prod D.μN)) < ∞ := hXi.2.1
  have f2 : (∫⁻ p, u_fX D.z' Ξ p ∂(D.μW'.prod D.μN)) < ∞ := hXi.2.2
  calc (∫⁻ p, ∫⁻ x, ‖Om D w₁ w₂ (p, x).1 * KM D F (p, x).1 (p, x).2‖ₑ ∂D.μG ∂D.μSS)
      ≤ ∫⁻ p, K * (u_fX D.z Ξ p.1 * u_fX D.z' Ξ p.2) ∂D.μSS := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_inSS D] with p hp
        exact hle p hp
    _ = K * ((∫⁻ p, u_fX D.z Ξ p ∂(D.μW.prod D.μN)) * ∫⁻ p, u_fX D.z' Ξ p ∂(D.μW'.prod D.μN)) := by
        rw [lintegral_const_mul' _ _ hK]
        unfold RealPlaceData.μSS
        rw [lintegral_prod_mul m1 m2]
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top (ENNReal.mul_lt_top f1 f2)
end Formalism.FourierDecayAlt.P.B7
