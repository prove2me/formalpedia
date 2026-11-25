-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.resSurj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:07.909868+00:00
-- url     : https://prove2.me/submissions/361a8aed-0890-4ca4-a555-1b4e830307b2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uw_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_conj
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_dec_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_leftG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_leftU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_rightG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_rightU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_dec_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_nlev_dec
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_conjN
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_conjW
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjW__4b27e7c5ccdf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_iH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_cF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_uL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_isOpen_adelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_cell_decomposition_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_Jx_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_mem_cell_domain_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_isOpen_cell_domain
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
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
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution : ResSurj := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D₁ φ Ψ hz hz' hD₁ hφ hΨ
  obtain ⟨hΨs, hΨL, hΨR, hΨW⟩ := hΨ
  refine ⟨D0 k r l D₁, ⟨isOpen_cell_domain hD₁.1, ?_⟩, ?_, ?_, Jx k r l z z' φ Ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
    have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
    have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
      simp only [Matrix.mul_assoc]
    rw [e]
    refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
    have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
    have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
    rw [e2]; exact h2
  · intro g hg
    exact hg.1.1
  · intro c hc g hg
    have d := dec_w (l := l) hc hg
    constructor
    · intro h
      have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
      rwa [d.rho_eq] at h2
    · intro h
      refine ⟨d.cell_decomposition_mem, ?_⟩
      show rho k r l (w1 k r l c * g) ∈ D₁
      rw [d.rho_eq]; exact h
  ·
    intro g₀ hg₀
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΨs g₁ ⟨d.hg, hg₁⟩
    refine ⟨C0 k r l ∩ rho k r l ⁻¹' U₁, fun g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
      (φ (cF k r l g) • F₁ (rho k r l g)), (smM_contDiffOn smM_rho).continuousOn.isOpen_inter_preimage isOpen_adelicUnipotentTimesIntegralOutsideSet hU₁,
      ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show rho k r l g₀ ∈ U₁
      rw [d.rho_eq]; exact hmem
    · have hs : C0 k r l ∩ rho k r l ⁻¹' U₁ ⊆ C0 k r l := Set.inter_subset_left
      have h1 := smM_id (C0 k r l ∩ rho k r l ⁻¹' U₁)
      have h2 : SmM (fun g => uL k r l g) (C0 k r l ∩ rho k r l ⁻¹' U₁) := smM_uL h1 fun x hx => hx.1.1
      have h3 : SmM (fun g => uL k r l (iH g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) := smM_uL (smM_iH h1) fun x hx => hx.1.2
      have h4 : ContDiffOn ℝ ∞ (fun g => φ (cF k r l g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) :=
        hφ.comp (sm_cF h1) fun x hx => hx.1.1
      have h5 : ContDiffOn ℝ ∞ (fun g => F₁ (rho k r l g)) (C0 k r l ∩ rho k r l ⁻¹' U₁) :=
        hF₁.comp ((smM_contDiffOn smM_rho).mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul (h4.smul h5)
    · intro g hgU hgG
      obtain ⟨u₂, g₂, u₂', d₂⟩ := dec_exists hgG hgU.1.1
      unfold Jx
      rw [hag (rho k r l g) hgU.2 (by rw [d₂.rho_eq]; exact d₂.hg)]
  ·
    intro g hg n hn
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    rw [Matrix.mul_assoc, d1.Jx_eq, d.Jx_eq, hΨL g₁ ⟨d.hg, hg₁⟩ n₁ hn₁,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    rw [← Matrix.mul_assoc, d1.Jx_eq, d.Jx_eq, hΨR g₁ ⟨d.hg, hg₁⟩ n₃ hn₃,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    rw [d1.Jx_eq, d.Jx_eq, hΨW g₁ ⟨d.hg, hg₁⟩ h hh h' hh', psi_conjW hz hh (up_nset d.hu),
      psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  · intro c hc g hg
    rw [(dec_w hc hg.1).Jx_eq, psi_one hz, psi_one hz', one_mul, one_smul]
end Formalism.FourierDecayAlt.P.Qx4
