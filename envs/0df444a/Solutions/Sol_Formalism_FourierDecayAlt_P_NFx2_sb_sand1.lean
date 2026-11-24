-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_sand1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:56.253821+00:00
-- url     : https://prove2.me/submissions/75139bdb-527c-47f1-948f-b9cb4cc5490b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_pj_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_projection_mul_coordinate

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (u v : ℂ) :
    proj κ σ * (QQ u 1 1 * QQ v 1 0) * proj κ ρ = L0.GG * (M.xC P σ u • lowerBlockAlt κ QQ σ ρ v) := by
  rw [diagonal_entry_hypothesis h, lowerBlockAlt]
  calc proj κ σ * (L0.GG * xA κ u * QQ v 1 0) * proj κ ρ
      = (proj κ σ * L0.GG) * xA κ u * QQ v 1 0 * proj κ ρ := by noncomm_ring
    _ = L0.GG * (proj κ σ * xA κ u) * QQ v 1 0 * proj κ ρ := by rw [sb_pj_GG h]; noncomm_ring
    _ = _ := by rw [projection_mul_coordinate]; simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
