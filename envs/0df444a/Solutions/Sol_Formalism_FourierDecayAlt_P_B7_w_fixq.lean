-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.w_fixq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:55.356802+00:00
-- url     : https://prove2.me/submissions/521e4bfb-ef7b-4976-9426-a9b0412bd1c4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_tr_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_tr_emb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_xi_tr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_normsq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_kint
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hk
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hkm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_meas_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hJ
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hW
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hOm

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hC : ConjInv D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (hint : Integrable (fun p => rho D p F (gq D q)) D.μSS) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2) volume ∧
    (((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS := by
  have hu : Integrable (fun p => hsVec (rho D p F (gq D q))) D.μSS := hsL.integrable_comp hint
  have hN : ∀ τ : ℝ × ℝ, (((‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p, ∫ p', xiTau D τ p' * KM D F p' (PhiM D (q, p)) ∂D.μSS ∂D.μSS := by
    intro τ
    rw [w_hJ D F _ hint τ]
    exact v_normsq D.inSS (ae_inSS D) tr (fun p hp => tr_mp D hC hp) (fun p hp => tr_emb D hp) _ hu
      (xiTau D τ) (w_meas_xi D τ) (norm_xi D τ) (fun p p' hp hp' => xi_tr D τ hp hp')
      (fun p p' => KM D F p' (PhiM D (q, p))) (fun p p' hp hp' => w_hk D F hq p p' hp hp')
  have hki := v_kint D.inSS (ae_inSS D) tr (fun p hp => tr_mp D hC hp) (fun p hp => tr_emb D hp) _ hu
      (fun p p' => KM D F p' (PhiM D (q, p))) (fun p p' hp hp' => w_hk D F hq p p' hp hp')
      (w_hkm D hF q).aestronglyMeasurable
  have sw := v_swap (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) (w_hW h₁ h₂) (xiTau D) (measurable_xi D)
    (norm_xi D) (fun p p' => KM D F p' (PhiM D (q, p))) hki
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
      ∫ p, ∫ p', xiTau D τ p' * KM D F p' (PhiM D (q, p)) ∂D.μSS ∂D.μSS =
      ((w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
    intro τ
    rw [← hN τ, ← Complex.ofReal_mul]
  simp_rw [e, w_hOm] at sw
  refine ⟨?_, ?_⟩
  · refine (sw.1.re).congr (ae_of_all _ fun τ => ?_)
    exact Complex.ofReal_re _
  · exact (integral_complex_ofReal).symm.trans sw.2
end Formalism.FourierDecayAlt.P.B7
