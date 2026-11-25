-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_sand2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:59.534022+00:00
-- url     : https://prove2.me/submissions/a370fcc6-8980-4dbb-b8d6-b37133771b59

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_pj_GG
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_pj__b_750f8a20ac4e
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_left_gamma_commutator
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_projection_mul_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_x_pj

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
    proj κ σ * (QQ v 1 0 * QQ u 1 1) * proj κ ρ =
      L0.GG * (M.xC P ρ u • lowerBlockAlt κ QQ σ ρ v - (M.xC P σ v * M.xC P ρ u) • (L0.ζb * (proj κ σ * proj κ ρ))) := by
  rw [diagonal_entry_hypothesis h, lowerBlockAlt]
  have e := lower_left_gamma_commutator h v
  rw [diagonal_entry_hypothesis h] at e
  calc proj κ σ * (QQ v 1 0 * (L0.GG * xA κ u)) * proj κ ρ
      = proj κ σ * (QQ v 1 0 * L0.GG) * (xA κ u * proj κ ρ) := by noncomm_ring
    _ = proj κ σ * (L0.GG * QQ v 1 0 - L0.GG * xA κ v * L0.ζb) * (M.xC P ρ u • proj κ ρ) := by rw [e, sb_x_pj]
    _ = M.xC P ρ u • ((proj κ σ * L0.GG) * QQ v 1 0 * proj κ ρ) -
          M.xC P ρ u • ((proj κ σ * L0.GG) * (xA κ v * L0.ζb) * proj κ ρ) := by
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_sub, mul_assoc]
    _ = M.xC P ρ u • (L0.GG * (proj κ σ * QQ v 1 0 * proj κ ρ)) -
          M.xC P ρ u • (L0.GG * ((proj κ σ * xA κ v) * L0.ζb * proj κ ρ)) := by
        rw [sb_pj_GG h]; simp only [mul_assoc]
    _ = _ := by
        rw [projection_mul_coordinate, smul_mul_assoc, smul_mul_assoc, sb_pj_ζb h]
        simp only [mul_sub, mul_smul_comm, smul_smul, mul_assoc]
        congr 1; rw [mul_comm (M.xC P σ v)]
end Formalism.FourierDecayAlt.P.NFx2
