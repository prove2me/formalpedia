-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_Bkap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:39:27.720046+00:00
-- url     : https://prove2.me/submissions/22d86e5b-75e8-4207-b449-1a8c29530921

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap

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
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) (f : M.Ty P → ℂ) :
    κ f * sc_B κ b = sc_B κ b * κ f := by
  unfold sc_B
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  calc κ f * (proj κ ρ * b ρ * proj κ ρ) = (κ f * proj κ ρ) * b ρ * proj κ ρ := by noncomm_ring
    _ = f ρ • (proj κ ρ * b ρ * proj κ ρ) := by rw [kap_mul_pj, smul_mul_assoc, smul_mul_assoc]
    _ = proj κ ρ * b ρ * (proj κ ρ * κ f) := by rw [pj_mul_kap, mul_smul_comm]
    _ = _ := by noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
