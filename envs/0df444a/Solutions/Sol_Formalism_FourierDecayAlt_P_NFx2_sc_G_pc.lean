-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_G_pc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:37.688902+00:00
-- url     : https://prove2.me/submissions/b9302f66-3cb7-4c67-9118-12c473770eda

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG
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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ : M.Ty P) :
    proj κ σ * (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) = (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) * proj κ σ := by
  have c1 : proj κ σ * xA κ Y = xA κ Y * proj κ σ := by unfold proj xA; exact kap_comm κ _ _
  rw [← mul_assoc, ← mul_assoc, sc_pf h σ (sc_mGG L0), mul_assoc L0.GG, c1, ← mul_assoc, mul_assoc _ (proj κ σ),
    connection_lowering_projection h hF, ← mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
