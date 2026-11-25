-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_K_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:16.710876+00:00
-- url     : https://prove2.me/submissions/56a35ea3-36df-4f58-92f2-499b405e7600

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_T_pj__ff5c34d09769

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
theorem _root_.solution (l : ℕ) (ρ' σ ρ : M.Ty P) :
    sb_K κ QQ l ρ' σ * proj κ ρ = if ρ' = ρ then sb_K κ QQ l ρ σ else 0 := by
  rw [sb_K, smul_mul_assoc, sb_T_pj']
  split_ifs with h
  · subst h; rfl
  · rw [smul_zero]
end Formalism.FourierDecayAlt.P.NFx2
