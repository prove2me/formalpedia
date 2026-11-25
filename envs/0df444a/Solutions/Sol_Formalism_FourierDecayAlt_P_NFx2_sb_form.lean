-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:46:20.642744+00:00
-- url     : https://prove2.me/submissions/be89b416-0219-4aa7-b2a1-d439fe4341ad

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_off
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_SS_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_K_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_lA_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_diag_form

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hP : P.OK) : SForm P L0 QQ κ (sb_b L0 κ QQ) (sb_SS κ QQ) := by
  intro Y hY ρ ρ'
  rw [sb_lA_blk h]
  by_cases hρ : ρ' = ρ
  · subst hρ
    rw [if_pos rfl, Finset.sum_eq_zero (fun l hl => if_neg (fun hu => up_ne P hl hu rfl)), add_zero,
      sb_diag_form h ρ' hY]
  · rw [if_neg hρ, zero_add]
    by_cases hex : ∃ l ∈ Icc 1 (P.k - 1), M.Up P l ρ ρ'
    · obtain ⟨l, hl, hup⟩ := hex
      rw [Finset.sum_eq_single l]
      · rw [if_pos hup, mul_assoc, sb_SS_pj hl hup, ← mul_smul_comm (Y + ((M.rho P ρ l : ℝ) : ℂ) + 1)⁻¹,
          sb_K_eval h hP hl hup hY, mul_smul_comm]
      · intro l' hl' hne
        rw [if_neg]; intro hup'; exact hne (up_idx P hl' hl hup' hup)
      · intro hl'; exact absurd hl hl'
    · rw [Finset.sum_eq_zero]
      · rcases sb_off h hP hρ with h0 | ⟨m, hm, hup, -⟩
        · rw [h0]; simp
        · exact absurd ⟨m, hm, hup⟩ hex
      · intro l hl; rw [if_neg]; intro hup; exact hex ⟨l, hl, hup⟩
end Formalism.FourierDecayAlt.P.NFx2
