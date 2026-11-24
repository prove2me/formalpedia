-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_lower_left_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:09.701447+00:00
-- url     : https://prove2.me/submissions/3712f8e4-530d-4d27-812b-f17eaa71c8b5

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_eq_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_ss_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_lreg
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_lup
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_lzero
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_projection_gamma_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {Y : ℂ} (hY : Reg P Y) :
    QQ Y 1 0 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 := by
  rw [connection_lower_left_entry]
  apply eq_of_blocks κ
  intro σ τ
  rw [sc_lreg h hY, mul_add, add_mul, lower_sum_block_entry hR, projection_gamma_coordinate h, projection_gamma_coordinate h, connection_lowering_block h hF]
  by_cases hst : σ = τ
  · subst hst
    rw [sc_ldiag hF hY, if_pos rfl, Finset.sum_eq_zero, add_zero]
    intro l hl
    rw [blk_ss κ hR l σ σ (fun hu => up_ne P hl hu rfl), smul_zero]
  · rw [if_neg hst, mul_zero, smul_zero, zero_add]
    by_cases hex : ∃ l ∈ Icc 1 (P.k - 1), M.Up P l τ σ
    · obtain ⟨l, hl, hu⟩ := hex
      rw [sc_lup hF hY hl hu, Finset.sum_eq_single l, pj_ss_pj κ hR hu, mul_smul_comm, ← mul_assoc, ← mul_assoc,
        L0.GG_GGi, one_mul, smul_smul]
      · congr 1
        have hx := sc_x_up hl hu Y
        have hne : (Y + (M.rho P τ l : ℂ) + 1) ≠ 0 := by
          intro h0; apply hY σ; rw [hx, h0, zero_mul]
        rw [hx]; field_simp
      · intro j hj hjl; rw [blk_ss κ hR j σ τ (fun hu' => hjl (up_idx P hj hl hu' hu)), smul_zero]
      · intro hn; exact absurd hl hn
    · push_neg at hex
      rw [sc_lzero hF hY hst (fun l hl => hex l hl), mul_zero, smul_zero, Finset.sum_eq_zero]
      intro l hl; rw [blk_ss κ hR l σ τ (hex l hl), smul_zero]
end Formalism.FourierDecayAlt.P.NFx2
