-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.qQZeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:01.94781+00:00
-- url     : https://prove2.me/submissions/a60de505-f1d4-4405-9fde-3f945a2e3ae2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lowering_constant_zeta_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_raising_constant_commute_zeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_S21_commute_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_sum_commute_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_quartic_sum_commute_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_commGroup_mul_eq_mul_mul_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution : QQZeta := by
  intro P Y
  have hg : Commute (ggA P) (zA P) := by
    unfold ggA zA ggP zP
    exact fn_comm P _ _ _ _
  have hgi : Commute (ggiA P) (zA P) := by
    unfold ggiA zA ggiP zP
    exact fn_comm P _ _ _ _
  have hx : Commute (xA P Y) (zA P) := by
    unfold xA zA
    exact kap_sc P _ _
  have hW : Commute (kap P fun π => wC P π Y) (zA P) := by
    unfold zA
    exact kap_sc P _ _
  have hS21 : Commute (weightedSumBis P Y) (zA P) := by
    unfold zA
    exact S21_commute_scalar P Y _
  have hS12 : Commute (S12 P Y) (zA P) := by
    unfold zA
    exact upper_sum_commute_scalar P Y _
  have hS4 : Commute (S4 P Y) (zA P) := by
    unfold zA
    exact quartic_sum_commute_scalar P Y _
  have hm := raising_constant_commute_zeta P Y
  have h1 := commGroup_mul_eq_mul_mul_div 0 (ggA P * xA P Y) (weightedSumBis P Y) 0 0 (l0A P Y) (zA P) (Commute.zero_left _)
    (hg.mul_left hx) hS21 (Commute.zero_left _) (Commute.zero_left _) (lowering_constant_zeta_comm P Y)
  simp only [zero_add, add_zero, zero_mul] at h1
  have h2 := commGroup_mul_eq_mul_mul_div (ggiA P * kap P fun π => wC P π Y) (ggA P * xA P Y * m0A P Y)
    (ggA P * m0A P Y * ggiA P * weightedSumBis P Y) (S12 P Y) (ggiA P * S4 P Y) (l0A P Y) (zA P)
    (hgi.mul_left hW) ((hg.mul_left hx).mul_left hm) (((hg.mul_left hm).mul_left hgi).mul_left hS21) hS12
    (hgi.mul_left hS4) (lowering_constant_zeta_comm P Y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold t21 t22
    exact h1
  · unfold t11 t12
    exact h2
  · unfold t12
    exact ((hg.mul_left hx).mul_left hm).add_left hS12
  · unfold t22
    exact hg.mul_left hx
end Formalism.FourierDecayAlt.P.Mx5
