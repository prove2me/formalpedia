-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_T_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:58.602383+00:00
-- url     : https://prove2.me/submissions/cbe35bcf-12b6-4f91-ac9c-33becd69a53c

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_orth
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem___f35113da0eee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem__b_76bdb2c4fd08
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_pj_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_x_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_comm_ops
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_crd_sub_ops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) {σ ρ : M.Ty P} (hne : σ ≠ ρ) (v : ℂ) :
    ∀ g ∈ L0.ops, Commute (lowerBlockAlt κ QQ σ ρ v) g := by
  obtain ⟨e1, -, -, -, e5, -⟩ := levelSubgroupAtPlace h v
  have hPz : ∀ τ, Commute (proj κ τ) L0.ζ := fun τ => H_kops h _ _ sb_mem_ζ
  have hPzb : ∀ τ, Commute (proj κ τ) L0.ζb := fun τ => H_kops h _ _ sb_mem_ζb
  have h22 : proj κ σ * QQ v 1 1 * proj κ ρ = 0 := by
    rw [diagonal_entry_hypothesis h, ← mul_assoc, sb_pj_GG h, mul_assoc, mul_assoc, sb_x_pj, mul_smul_comm,
      pj_orth κ hne, smul_zero, mul_zero]
  apply sb_comm_ops
  · show lowerBlockAlt κ QQ σ ρ v * L0.ζ = L0.ζ * lowerBlockAlt κ QQ σ ρ v
    rw [lowerBlockAlt, mul_assoc, (hPz ρ).eq, ← mul_assoc, mul_assoc (proj κ σ), e1, mul_sub, sub_mul, h22, sub_zero,
      ← mul_assoc, (hPz σ).eq]
    simp only [mul_assoc]
  · show lowerBlockAlt κ QQ σ ρ v * L0.ζb = L0.ζb * lowerBlockAlt κ QQ σ ρ v
    rw [lowerBlockAlt, mul_assoc, (hPzb ρ).eq, ← mul_assoc, mul_assoc (proj κ σ), e5, ← mul_assoc, (hPzb σ).eq]
    simp only [mul_assoc]
  · intro g hg
    have hp : ∀ τ, Commute (proj κ τ) g := fun τ => H_kops h _ _ (sb_crd_sub_ops hg)
    exact ((hp σ).mul_left (H_crd h v 1 0 g hg)).mul_left (hp ρ)
end Formalism.FourierDecayAlt.P.NFx2
