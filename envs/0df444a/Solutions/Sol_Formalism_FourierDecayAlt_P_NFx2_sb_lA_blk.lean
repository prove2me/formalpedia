-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_lA_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:54.913491+00:00
-- url     : https://prove2.me/submissions/6e971a87-5e1d-4df3-a811-7c7fe106e09e

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_pj_GGi

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (Y : ℂ) :
    proj κ σ * lA L0 QQ κ Y * proj κ ρ = (M.xC P σ Y)⁻¹ • (L0.GGi * lowerBlockAlt κ QQ σ ρ Y) := by
  unfold lA xiA
  rw [← mul_assoc, ← mul_assoc, pj_mul_kap, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, sb_pj_GGi h, lowerBlockAlt]
  simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
