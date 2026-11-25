-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_diag_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:56.795891+00:00
-- url     : https://prove2.me/submissions/055c6855-447e-41fd-acf7-d0a1ad4fe103

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GGi__b_1df21f612a80
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_T_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_regular_base_point_reg

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {Y : ℂ} (hY : Reg P Y) :
    (sb_b L0 κ QQ ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ = (M.xC P ρ Y)⁻¹ • (L0.GGi * lowerBlockAlt κ QQ ρ ρ Y) := by
  have e := sb_diag h ρ (regular_base_point_reg ρ) (hY ρ)
  have e1 : sb_b L0 κ QQ ρ * proj κ ρ = L0.GGi * ((M.xC P ρ regular_base_point)⁻¹ • lowerBlockAlt κ QQ ρ ρ regular_base_point + regular_base_point • (L0.ζb * proj κ ρ)) := by
    rw [sb_b, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, sb_T_pj, mul_assoc, pj_idem]
  rw [sub_mul, e1, e, smul_mul_assoc, mul_assoc,
    show L0.ζb * (L0.GGi * proj κ ρ) = L0.GGi * (L0.ζb * proj κ ρ) by rw [← mul_assoc, ← sb_GGi_ζb, mul_assoc],
    mul_add, mul_smul_comm, mul_smul_comm]
  abel
end Formalism.FourierDecayAlt.P.NFx2
