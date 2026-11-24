-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_lowering_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:54.052625+00:00
-- url     : https://prove2.me/submissions/6c3bc116-dd66-411d-bce0-a21c73b54321

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_B_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_projection

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ τ : M.Ty P) :
    proj κ σ * (sc_LL h hF).l0 Y * proj κ τ = if σ = τ then (b σ - Y • (L0.ζb * L0.GGi)) * proj κ σ else 0 := by
  rw [connection_lowering_projection, mul_assoc]
  split_ifs with hst
  · subst hst; rw [pj_idem, connection_lowering_eq, sub_mul, sc_B_pj h hF, smul_mul_assoc, sub_mul, smul_mul_assoc]
  · rw [pj_orth κ hst, mul_zero]
end Formalism.FourierDecayAlt.P.NFx2
