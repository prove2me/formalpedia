-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.y_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:18:55.57936+00:00
-- url     : https://prove2.me/submissions/698bfe3d-437f-4621-b108-e70e38b94a0b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_or_weight_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurableSet_Qset
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_hsL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_JM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_ae_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_fixq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_boundary_weight_nonneg

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
attribute [local instance] sfNu
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) (hC : ConjInv D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 ∨
      (Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2) volume ∧
        ((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2 : ℝ) : ℂ) =
          ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS) := by
  have h1 := (ae_restrict_iff' (measurableSet_Qset D)).1 (jc_ae_integrable D hI hCC hF)
  filter_upwards [h1, ae_mem_good_set_or_weight_zero D] with q hq1 hq2
  rcases hq2 with h | h
  · by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
    · exact Or.inl hw
    · right
      have hQ : q ∈ Qset D := lt_of_le_of_ne (boundary_weight_nonneg _ _ q) (Ne.symm hw)
      have := w_fixq D hC (jc_cont hF) h (hq1 hQ) h₁ h₂
      simp_rw [JM_eq D F _ h, hsL_apply]
      exact this
  · exact Or.inl h
end Formalism.FourierDecayAlt.P.B7
