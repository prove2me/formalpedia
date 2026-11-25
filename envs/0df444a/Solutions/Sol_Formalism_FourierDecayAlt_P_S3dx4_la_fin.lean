-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.la_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:02.575006+00:00
-- url     : https://prove2.me/submissions/3f80f84e-d299-466d-b0e7-073482e3d45c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gNpow_inCC
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ae_SS
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_map_invP
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_rho_triv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_integral_converges
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_closed
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
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hNI : NormInv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] {b : ℝ} (hb : JF.TransportedAlt k r b 0) (hb0 : b ≠ 0)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
      ∂D.μSS < ⊤ := by
  set F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hF
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) b F hb (gNpow_inCC hNI b hb0)
  obtain ⟨bb, hbb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
  set G : B.SS k r → ℝ≥0∞ := fun p => ‖B.gN (B.sgs p γ) ^ (-b)‖ₑ with hG
  have h1 : ∫⁻ p, G p ∂D.μSS < ⊤ := by
    calc ∫⁻ p, G p ∂D.μSS ≤ ∫⁻ p, ‖bb p‖ₑ ∂D.μSS := by
          apply lintegral_mono_ae
          filter_upwards [hbd γ rfl] with p hp
          have e : ‖B.gN (B.sgs p γ) ^ (-b)‖ = ‖B.rho (triv D) p F γ‖ := by
            rw [rho_triv]; simp [hF]
          simp only [hG]
          rw [← ofReal_norm, ← ofReal_norm, e]
          exact ENNReal.ofReal_le_ofReal (hp.trans (Real.le_norm_self _))
      _ < ⊤ := hbb.hasFiniteIntegral
  have hinv : ∀ᵐ p ∂D.μSS, invP (invP p) = p ∧
      G (invP p) = ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ *
        (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ := by
    filter_upwards [ae_SS D] with p hp
    have u1 := (weyl_subgroup_closed k r D.z).unit _ hp.1
    have u2 := (unipotent_radical_closed k r).unit _ hp.2.1
    have u3 := (weyl_subgroup_closed k r D.z').unit _ hp.2.2.1
    have u4 := (unipotent_radical_closed k r).unit _ hp.2.2.2
    have ii : ∀ x : Formalism.QuantumDeterminants.Mt k r, IsUnit (Matrix.of x).det → B2.invM (B2.invM x) = x := by
      intro x hx
      show (((Matrix.of x)⁻¹)⁻¹ : B.Mat k r) = Matrix.of x
      exact Matrix.nonsing_inv_nonsing_inv _ hx
    refine ⟨?_, ?_⟩
    · simp only [invP]
      rw [ii _ u1, ii _ u2, ii _ u3, ii _ u4]
    · simp only [hG, invP, B.sgs]
      have j1 : (Matrix.of (B2.invM p.1.1))⁻¹ = Matrix.of p.1.1 := ii _ u1
      have j2 : (Matrix.of (B2.invM p.1.2))⁻¹ = Matrix.of p.1.2 := ii _ u2
      rw [j1, j2]
      rfl
  calc ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
        ∂D.μSS = ∫⁻ p, G (invP p) ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => hp.2.symm)
    _ = ∫⁻ p, G (invP p) ∂(D.μSS.map invP) := by rw [map_invP D]
    _ ≤ ∫⁻ p, G (invP (invP p)) ∂D.μSS := lintegral_map_le (fun p => G (invP p)) invP
    _ = ∫⁻ p, G p ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => by show G (invP (invP p)) = G p; rw [hp.1])
    _ < ⊤ := h1
end Formalism.FourierDecayAlt.P.S3dx4
