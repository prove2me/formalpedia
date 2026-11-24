-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.QQr_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:29.672681+00:00
-- url     : https://prove2.me/submissions/9bc56b22-ba56-487f-b80e-ac087fcbcc8a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_star_mem_Cen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_kap_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_SS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_z_mem

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
theorem _root_.solution (P : Par) (i : Fin P.r) (Y : ℂ) : Ent (Cen P i) (QQr P Y) := by
  have hz : zA P ∈ Cen P i := z_mem P i _ (by simp)
  have hzb : zbA P ∈ Cen P i := z_mem P i _ (by simp)
  have hgg : ggA P ∈ Cen P i := z_mem P i _ (by simp)
  have hggi : ggiA P ∈ Cen P i := z_mem P i _ (by simp)
  have hnab : nabA P ∈ Cen P i := z_mem P i _ (by simp)
  have hnabs : nabsA P ∈ Cen P i := z_mem P i _ (by simp)
  have hk := kap_mem P i
  have hS := SS_mem P i
  have hSs : ∀ l, star (SS P l) ∈ Cen P i := fun l => star_mem_Cen (hS l)
  have hl0 : l0A P Y ∈ Cen P i :=
    sub_mem (neg_mem hnab) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hggi))
  have hm0 : m0A P Y ∈ Cen P i :=
    sub_mem (neg_mem hnabs) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hggi))
  have hx : xA P Y ∈ Cen P i := hk _
  have h21 : weightedSumBis P Y ∈ Cen P i := sum_mem fun l _ => mul_mem (hS l) (hk _)
  have h12 : S12 P Y ∈ Cen P i := sum_mem fun l _ => mul_mem (hk _) (hSs l)
  have h4 : S4 P Y ∈ Cen P i :=
    sum_mem fun l _ => sum_mem fun j _ => mul_mem (mul_mem (hSs l) (hS j)) (hk _)
  intro a b
  fin_cases a <;> fin_cases b
  · show t11 P Y ∈ Cen P i
    exact add_mem (add_mem (add_mem (add_mem (mul_mem hggi (hk _))
      (mul_mem (mul_mem (mul_mem hgg hx) hm0) hl0)) (mul_mem (mul_mem (mul_mem hgg hm0) hggi) h21))
      (mul_mem h12 hl0)) (mul_mem hggi h4)
  · show t12 P Y ∈ Cen P i
    exact add_mem (mul_mem (mul_mem hgg hx) hm0) h12
  · show t21 P Y ∈ Cen P i
    exact add_mem (mul_mem (mul_mem hgg hx) hl0) h21
  · show t22 P Y ∈ Cen P i
    exact mul_mem hgg hx
end Formalism.FourierDecayAlt.P.Mx8
