-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:39.821857+00:00
-- url     : https://prove2.me/submissions/102367f3-905d-4278-b4d7-2bf4c1ec6b92

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_feq

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {u v : ℂ} (hu : M.xC P ρ u ≠ 0) (hv : M.xC P ρ v ≠ 0) :
    (M.xC P ρ u)⁻¹ • lowerBlockAlt κ QQ ρ ρ u + u • (L0.ζb * proj κ ρ) =
      (M.xC P ρ v)⁻¹ • lowerBlockAlt κ QQ ρ ρ v + v • (L0.ζb * proj κ ρ) := by
  have e := sb_feq h ρ ρ u v
  rw [pj_idem] at e
  have key : (M.xC P ρ u * M.xC P ρ v) • ((M.xC P ρ u)⁻¹ • lowerBlockAlt κ QQ ρ ρ u + u • (L0.ζb * proj κ ρ)) =
      (M.xC P ρ u * M.xC P ρ v) • ((M.xC P ρ v)⁻¹ • lowerBlockAlt κ QQ ρ ρ v + v • (L0.ζb * proj κ ρ)) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show M.xC P ρ u * M.xC P ρ v * (M.xC P ρ u)⁻¹ = M.xC P ρ v by field_simp,
      show M.xC P ρ u * M.xC P ρ v * (M.xC P ρ v)⁻¹ = M.xC P ρ u by field_simp]
    linear_combination (norm := module) e
  exact smul_right_injective A (mul_ne_zero hu hv) key
end Formalism.FourierDecayAlt.P.NFx2
