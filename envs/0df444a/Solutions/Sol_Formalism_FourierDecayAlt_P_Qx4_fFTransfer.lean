-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.fFTransfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:51.415679+00:00
-- url     : https://prove2.me/submissions/b32bef9e-c6e8-4573-b848-24cb74d01b7e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uw_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_level_one_eq_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_blk_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lev_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lev_uw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lift_inWb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_cont_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_blk_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_lev_mul
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
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution : FFTransfer := by
  intro Wp Wq _ _ _ _ k r' z z' π π' D hz hz' hD J hJ
  obtain ⟨hJs, hJL, hJR, hJW⟩ := hJ
  refine ⟨fun x => π (blk x), fun x => π' (blk x), (fun x : Mx k (1 + r') => (blk x : Mx k r')) ⁻¹' D,
    fun x => J (blk x), lift_inWb hz, lift_inWb hz', ⟨hD.1.preimage cont_blk, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro x hx s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨h₁, hh₁, rfl⟩ := level_one_eq_embedding (uw_glev hh _)
    obtain ⟨m₁, hm₁, rfl⟩ := level_one_eq_embedding hm.2
    obtain ⟨h₂, hh₂, rfl⟩ := level_one_eq_embedding (uw_glev hh' _)
    obtain ⟨m₂, hm₂, rfl⟩ := level_one_eq_embedding hm'.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    show blk (ιLev k 1 r' h₁ * ιLev k 1 r' m₁ * ιLev k 1 r' g * (ιLev k 1 r' h₂ * ιLev k 1 r' m₂)) ∈ D
    rw [← B2x8.al_lev_mul, ← B2x8.al_lev_mul, ← B2x8.al_lev_mul, ← B2x8.al_lev_mul, blk_lev]
    exact hD.2 g ⟨glev0 hg, hgD⟩ (h₁ * m₁) ⟨h₁, lev_uw hh₁ hh, m₁, ⟨lev_nset hm₁ hm.1, glev0 hm₁⟩, rfl⟩
      (h₂ * m₂) ⟨h₂, lev_uw hh₂ hh', m₂, ⟨lev_nset hm₂ hm'.1, glev0 hm₂⟩, rfl⟩
  · intro x₀ hx₀
    obtain ⟨g₀, hg₀, rfl⟩ := level_one_eq_embedding hx₀.1
    have hgD : g₀ ∈ D := by
      have := hx₀.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    obtain ⟨U, F, hU, hmem, hF, hag⟩ := hJs g₀ ⟨glev0 hg₀, hgD⟩
    refine ⟨(fun x : Mx k (1 + r') => (blk x : Mx k r')) ⁻¹' U, fun x => F (blk x), hU.preimage cont_blk, ?_, ?_, ?_⟩
    · simp only [Set.mem_preimage, blk_lev]; exact hmem
    · exact hF.comp (smM_contDiffOn (smM_blk _)) fun x hx => hx
    · intro x hxU hxG
      obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hxG
      simp only [Set.mem_preimage, blk_lev] at hxU
      simp only [blk_lev]
      exact hag g hxU (glev0 hg)
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨n₁, hn₁, rfl⟩ := level_one_eq_embedding hn.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, psi_lev]
    simp only [blk_lev]
    exact hJL g ⟨glev0 hg, hgD⟩ n₁ ⟨lev_nset hn₁ hn.1, glev0 hn₁⟩
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨n₁, hn₁, rfl⟩ := level_one_eq_embedding hn.2
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, psi_lev]
    simp only [blk_lev]
    exact hJR g ⟨glev0 hg, hgD⟩ n₁ ⟨lev_nset hn₁ hn.1, glev0 hn₁⟩
  · intro x hx h hh h' hh'
    obtain ⟨g, hg, rfl⟩ := level_one_eq_embedding hx.1
    obtain ⟨h₁, hh₁, rfl⟩ := level_one_eq_embedding (uw_glev hh _)
    obtain ⟨h₂, hh₂, rfl⟩ := level_one_eq_embedding (uw_glev hh' _)
    have hgD : g ∈ D := by
      have := hx.2
      simp only [Set.mem_preimage, blk_lev] at this
      exact this
    rw [← B2x8.al_lev_mul, ← B2x8.al_lev_mul]
    simp only [blk_lev]
    exact hJW g ⟨glev0 hg, hgD⟩ h₁ (lev_uw hh₁ hh) h₂ (lev_uw hh₂ hh')
  · intro g _
    simp only [Set.mem_preimage, blk_lev, true_and, iff_self]
end Formalism.FourierDecayAlt.P.Qx4
