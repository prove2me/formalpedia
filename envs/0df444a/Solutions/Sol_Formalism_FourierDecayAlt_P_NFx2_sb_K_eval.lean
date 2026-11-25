-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_K_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:06.087197+00:00
-- url     : https://prove2.me/submissions/6188a8a8-ba32-4e1a-a338-2e438f306b5a

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_off
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_regular_base_point_reg
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_up_factor

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hP : P.OK) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P}
    (hup : M.Up P l ρ σ) {Y : ℂ} (hY : Reg P Y) :
    (Y + ((M.rho P ρ l : ℝ) : ℂ) + 1)⁻¹ • sb_K κ QQ l ρ σ = (M.xC P σ Y)⁻¹ • lowerBlockAlt κ QQ σ ρ Y := by
  have hne : σ ≠ ρ := fun e => up_ne P hl hup e.symm
  have hσl : M.rho P σ l = M.rho P ρ l + 1 := by
    have := up_rho P hup l hl; simpa using this
  have hfac : ∀ Z : ℂ, Reg P Z → Z + ((M.rho P ρ l : ℝ) : ℂ) + 1 ≠ 0 := by
    intro Z hZ
    have := sb_up_factor (hZ σ) hl
    rw [hσl] at this; push_cast at this; rwa [← add_assoc] at this
  rcases sb_off h hP hne with h0 | ⟨m, hm, hupm, K, hK⟩
  · simp [sb_K, h0]
  · have hml : m = l := up_idx P hm hl hupm hup
    subst hml
    have h0 := regular_base_point_reg (P := P)
    have hKK : sb_K κ QQ m ρ σ = K := by
      rw [sb_K, div_eq_mul_inv, mul_comm, ← smul_smul, hK regular_base_point, smul_smul, inv_mul_cancel₀ (h0 σ), one_smul]
    have hTY : lowerBlockAlt κ QQ σ ρ Y = ((Y + ((M.rho P ρ m : ℝ) : ℂ) + 1)⁻¹ * M.xC P σ Y) • K := by
      rw [← smul_smul, ← hK Y, smul_smul, inv_mul_cancel₀ (hfac Y hY), one_smul]
    rw [hKK, hTY, smul_smul]
    congr 1
    field_simp [hY σ]
end Formalism.FourierDecayAlt.P.NFx2
