-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.orbConvDD_of_decDD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:28.743093+00:00
-- url     : https://prove2.me/submissions/b0e87ca5-252d-4d0f-a36c-1a5f184c957e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_thr_of_gapOK
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_aOf_pos_of_gapOK
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_rho_triv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_rpow_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ckOn_zero_of_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_sigma_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_integral_converges
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_integral_domain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hD : DecDD) : OrbConvDD := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS hS' x hx y hy
  obtain ⟨C, hC⟩ :=
    hD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS y hy x hx
  have hG : GapOK k r h := hS.2.2.2.1
  have hσ : PI.UpqRep.IsDSHpk k r ε lam σ := hS.2.1
  have hThr : JF.TransportedAlt k r (aOf r h) 0 := thr_of_gapOK hG
  have ha : aOf r h ≠ 0 := (aOf_pos_of_gapOK hG).ne'
  let f : Mx k r → ℂ := fun g => ⟪x, σ g y⟫_ℂ
  have hfc : ContinuousOn f (B.GV k r) :=
    ContinuousOn.inner continuousOn_const (sigma_contOn hσ y)
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => f g • (1 : ℂ →L[ℂ] ℂ)
  have hCC : B.InCC (aOf r h) 0 F := by
    refine ⟨|C|, ckOn_zero_of_contOn f hfc, ?_⟩
    intro uu vv _ _ hlen g hg
    have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu; subst hv
    show B.gN g ^ aOf r h * ‖F g‖ ≤ |C|
    have hF : ‖F g‖ = ‖f g‖ := by simp [F]
    rw [hF]
    have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc B.gN g ^ aOf r h * ‖f g‖ ≤ B.gN g ^ aOf r h * (C * B.gN g ^ (-aOf r h)) :=
          mul_le_mul_of_nonneg_left (hC g hg) (Real.rpow_nonneg hgN _)
      _ ≤ |C| := rpow_bound _ _ _ hgN ha
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) (aOf r h) F hThr hCC
  have hJD := Formalism.FourierDecayAlt.P.bessel_integral_domain k r ℂ ℂ (triv D) (aOf r h) 0 F hThr hCC
  have hnorm : ∀ p γ, ‖⟪x, σ (B.sgs p γ) y⟫_ℂ‖ = ‖B.rho (triv D) p F γ‖ := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  have happ : ∀ p γ, ⟪x, σ (B.sgs p γ) y⟫_ℂ = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (B.rho (triv D) p F γ) := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  refine ⟨fun γ hγ => ?_, fun K hK hKO => ?_⟩
  · obtain ⟨b, hb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
    have hmeas : AEStronglyMeasurable (fun p => B.rho (triv D) p F γ) D.μSS :=
      hJD.1 [] [] (by simp) (by simp) (by simp) γ hγ
    have hmeas' : AEStronglyMeasurable (fun p => ⟪x, σ (B.sgs p γ) y⟫_ℂ) D.μSS := by
      have := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_aestronglyMeasurable hmeas
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (happ p γ).symm
    refine Integrable.mono' hb hmeas' ?_
    filter_upwards [hbd γ rfl] with p hp
    rw [hnorm]
    exact hp
  · obtain ⟨b, hb, hbd⟩ := hJC.2 K hK hKO
    refine ⟨b, hb, fun γ hγ => ?_⟩
    filter_upwards [hbd γ hγ] with p hp
    rw [hnorm]
    exact hp
end Formalism.FourierDecayAlt.P.S3dx4
