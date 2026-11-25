-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.phi_Ffull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:15.100909+00:00
-- url     : https://prove2.me/submissions/76ca82da-fcdc-4f13-a280-02a6d7104e5a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_tiePhi_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_eta
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_TM_setTies_deg_eta
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f) =
      rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))
        (tiePhiAt p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (Fin.castSucc (Fin.last (T.pos i)))
          (Fin.last (T.pos i + 1)) (T.z i) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)) := by
  have hK := hK_of_adm LL T hadm i
  have h : T.pos i + 1 < N := by omega
  rw [Ffull_eq]
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  rw [← tiePhi_rename _ (inclusion_prodMap_injective hK)]
  have e1 : ιF N (T.pos i + 1) (Fin.castSucc (Fin.last (T.pos i))) = ⟨T.pos i, by omega⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have e2 : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, h⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have d1 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.castSucc (Fin.last (T.pos i))) =
      (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_castSucc]
    simp [Letters.takeD, (by omega : T.pos i < N)]
  have d2 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.last (T.pos i + 1)) =
      (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_last, setTies_deg_eta LL T hadm i n h]
  rw [d1, d2]
  simp only [e1, e2]
end Formalism.CountingSumsFrames.TO
