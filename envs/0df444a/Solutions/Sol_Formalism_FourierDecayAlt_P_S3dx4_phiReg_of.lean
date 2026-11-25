-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.phiReg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:38.938742+00:00
-- url     : https://prove2.me/submissions/9b160308-ec02-4252-a1f8-4e9627da3c4b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ag_lt_a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_DD_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_ae_UH_of_quot
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_muSof_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_be_enorm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_dd_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_l1_quotient_integral_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_l_of_be
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
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hSch : SchurH) (hNI : NormIdSm) (hGG : GrowthG) (hDD : DecDD) (hBC : BeConv) :
    More.PhiReg := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hbe x hx
  have hS' := hS
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS'
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hl hds hw0 x hx
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  · obtain ⟨v, hv, hlv⟩ := hA
    set cc : ℂ := ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ with hcc
    have hlx : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        l (σ g x) = cc • (be z c π σ μW μN (σ g x) v) (l v) :=
      fun g hg => l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv
    refine ⟨?_, ?_, ?_⟩
    · have hc := (hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS).2.2.1 x hxs v (Or.inl hv)
      have hc2 : ContinuousOn (fun g => cc • (ContinuousLinearMap.apply ℂ Wp (l v))
          (be z c π σ μW μN (σ g x) v)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
        ((ContinuousLinearMap.apply ℂ Wp (l v)).continuous.comp_continuousOn hc).const_smul cc
      exact hc2.congr (fun g hg => hlx g hg)
    · obtain ⟨C, hC⟩ := hDD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv
      have hI := hGG k r μG (aOf r h) hGm (ag_lt_a hG)
      have hfin := l1_quotient_integral_bound hds hW hN hGm hq hC hI
      have hb : ∀ᵐ g ∂νq, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ≤
          (‖cc‖ₑ * ‖l v‖ₑ) * ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
        filter_upwards [hae] with g hg
        rw [← enorm_eq_nnnorm, hlx _ hg]
        have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
        calc ‖cc • (be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ
            = ‖cc‖ₑ * ‖(be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ := enorm_smul _ _
          _ ≤ ‖cc‖ₑ * (‖be z c π σ μW μN (σ (Matrix.of g) x) v‖ₑ * ‖l v‖ₑ) := by
            gcongr
            exact ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖cc‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
              ‖l v‖ₑ) := by gcongr
          _ = _ := by ring
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq
          ≤ ∫⁻ g, (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_mono_ae hb
        _ = (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ g, ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])
        _ < ⊤ := ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) hfin
    · have hN2 := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hxs v (Or.inl hv) (l v)).1
      have hfin : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v (l v)) < ⊤ := by
        rw [hN2]; exact ENNReal.ofReal_lt_top
      unfold PI.BesselPeriodGGP.l2SG at hfin ⊢
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq
          = ∫⁻ g, ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq := by
            apply lintegral_congr_ae
            filter_upwards [hae] with g hg
            rw [hlx _ hg, nnnorm_smul, ENNReal.coe_mul, mul_pow]
        _ = ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ∫⁻ g, ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq :=
            lintegral_const_mul' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin
  · push Not at hA
    have hz : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ g x) = 0 :=
      fun g hg => hA _ (dd_stable hds hg x hx)
    refine ⟨?_, ?_, ?_⟩
    · exact (continuousOn_const (c := (0 : Wp))).congr (fun g hg => hz g hg)
    · have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top
    · unfold PI.BesselPeriodGGP.l2SG
      have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top
end Formalism.FourierDecayAlt.P.S3dx4
