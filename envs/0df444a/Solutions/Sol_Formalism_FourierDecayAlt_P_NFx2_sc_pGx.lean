-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_pGx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:40:53.107467+00:00
-- url     : https://prove2.me/submissions/73aa3161-be18-4122-99db-36a843438d4e

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (σ : M.Ty P) (Y : ℂ) (X : A) :
    proj κ σ * (L0.GG * xA κ Y * X) = M.xC P σ Y • (L0.GG * (proj κ σ * X)) := by
  rw [← mul_assoc, ← mul_assoc, sc_pf h σ (sc_mGG L0), mul_assoc L0.GG, xA, pj_mul_kap, mul_smul_comm,
    smul_mul_assoc, mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
