-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.startOK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:49:24.136799+00:00
-- url     : https://prove2.me/submissions/de67a83e-46f0-4d2a-811b-d98718238d06

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_fn_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_coordinate_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kap_comm_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kap_comm_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kappa_sign_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_low_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (hS : StartIsStart) (hT : T21Commute) (hSc : SSScalar) (hSh : SSShift) (hRho : RhoUp) :
    StartOK := by
  intro P hP l L hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  have hzf : ∀ g ∈ zfns L, ∃ w, g = sc P w := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨zP, hz⟩
    · exact ⟨ziP, hzi⟩
    · exact ⟨zbP, hzb⟩
    · exact ⟨zbiP, hzbi⟩
    · exact ⟨ggP P.TT, hgg⟩
    · exact ⟨ggiP P.TT, hggi⟩
  refine ⟨hS P hP l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Y'
    show Commute (sgn P l • t21 P Y) (sgn P l • t21 P Y')
    exact ((hT P hP Y Y').smul_left _).smul_right _
  · intro Y hY
    have hne : ∀ π, x0 P l π Y ≠ 0 := fun π =>
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)
    have h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ) := by
      funext π; exact mul_inv_cancel₀ (hne π)
    have h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ) := by
      funext π; exact inv_mul_cancel₀ (hne π)
    refine ⟨?_, ?_⟩
    · show (kap P fun π => x0 P l π Y) * (kap P fun π => (x0 P l π Y)⁻¹) = 1
      rw [← map_mul, h1, map_one]
    · show (kap P fun π => (x0 P l π Y)⁻¹) * (kap P fun π => x0 P l π Y) = 1
      rw [← map_mul, h2, map_one]
  · intro Y Y'
    exact kap_comm_kap P _ _
  · intro Y g hg
    obtain ⟨w, rfl⟩ := hzf g hg
    exact kap_comm_sc P _ w
  · intro Y
    rw [hnab]
    exact kap_comm_diag P _ _
  · intro Y hY
    show star (kap P fun π => x0 P l π Y) = kap P fun π => x0 P l π Y
    rw [star_kap]
    congr 1
    funext π
    exact coordinate_real P l π Y hY
  · intro Y g hg
    have h1 : Commute (zA P) g := by
      rw [← hz]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h2 : Commute (zbiA P) g := by
      rw [← hzbi]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) g := by
      obtain ⟨w, hw⟩ := hzf g hg
      rw [hw]
      exact Commute.sum_left _ _ _ fun j _ => (kap_comm_sc P _ w).mul_left (hSc P j w)
    exact (h1.mul_left h2).mul_left h3
  · intro Y
    show sgn P l • (ggA P * xA P Y) = L.GG * kap P (fun π => x0 P l π Y)
    rw [kappa_sign_coordinate, mul_smul_comm, hgg]
  · intro Y hY
    have hl0 : L.l0 Y = l0A P Y := by simp only [LevelData.l0, l0A, hnab, hzb, hggi]
    have hcan := fn_cancel L
    have hgi := L.GG_GGi
    rw [hzb, hzi, hggi, hz, hzbi] at hcan
    rw [hgg, hggi] at hgi
    have hcx : ggA P * xA P Y = xA P Y * ggA P := (kap_comm_sc P _ _).eq.symm
    show sgn P l • (ggA P * xA P Y * l0A P Y + weightedSumBis P Y) =
      L.GG * (kap P fun π => x0 P l π Y) * (L.l0 Y + L.ζb * L.ζi * L.GGi * eeA P Y)
    rw [hl0, kappa_sign_coordinate, hgg, hzb, hzi, hggi, ← low_sum hSh hRho P Y hY, eeA, ← mul_assoc _ (zA P * zbiA P), hcan,
      mul_smul_comm, smul_mul_assoc, mul_add]
    congr 2
    rw [hcx, mul_assoc, ← mul_assoc (ggA P), hgi, one_mul]
end Formalism.FourierDecayAlt.P.Mx8
