-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_feq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:39.658464+00:00
-- url     : https://prove2.me/submissions/75e5276c-9720-4e99-9f8b-3528e0275c27

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_rtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_sand1
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_sand2

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
    (u - v) • (M.xC P σ u • lowerBlockAlt κ QQ σ ρ v -
      (M.xC P ρ u • lowerBlockAlt κ QQ σ ρ v - (M.xC P σ v * M.xC P ρ u) • (L0.ζb * (proj κ σ * proj κ ρ)))) =
      M.xC P σ u • lowerBlockAlt κ QQ σ ρ v - M.xC P σ v • lowerBlockAlt κ QQ σ ρ u := by
  have r := H_rtt h u v 1 1 1 0
  have r2 := congrArg (fun Z => L0.GGi * (proj κ σ * Z * proj κ ρ)) r
  simp only [smul_sub, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc] at r2
  rw [sb_sand1 h, sb_sand2 h, sb_sand1 h] at r2
  have cancel : ∀ Z : A, L0.GGi * (L0.GG * Z) = Z := fun Z => by rw [← mul_assoc, L0.GGi_GG, one_mul]
  simp only [cancel] at r2
  rw [smul_sub]
  exact r2
end Formalism.FourierDecayAlt.P.NFx2
