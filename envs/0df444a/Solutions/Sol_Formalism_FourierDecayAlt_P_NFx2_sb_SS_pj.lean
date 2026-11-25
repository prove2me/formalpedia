-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_SS_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:03.648949+00:00
-- url     : https://prove2.me/submissions/9c307598-68af-450b-9bf2-3e1f99562586

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_K_pj

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
theorem _root_.solution {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P} (hup : M.Up P l ρ σ) :
    sb_SS κ QQ l * proj κ ρ = sb_K κ QQ l ρ σ := by
  rw [sb_SS, Finset.sum_mul, Finset.sum_eq_single ρ]
  · rw [Finset.sum_mul, Finset.sum_eq_single σ]
    · rw [if_pos ⟨hl, hup⟩, sb_K_pj, if_pos rfl]
    · intro σ' _ hσ'
      rw [if_neg]; · rw [zero_mul]
      rintro ⟨-, hup'⟩; exact hσ' (up_right P hup' hup)
    · simp
  · intro ρ' _ hρ'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun σ' _ => ?_
    split_ifs
    · rw [sb_K_pj, if_neg hρ']
    · rw [zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.NFx2
