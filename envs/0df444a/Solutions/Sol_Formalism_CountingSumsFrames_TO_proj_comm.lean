-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.proj_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:27.19124+00:00
-- url     : https://prove2.me/submissions/27809944-adb0-44c1-a9aa-21d68c5b954c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
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
open Formalism.GM.DimensionMonotonicity Finset
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {W : Submodule K V} {ι : Type*} (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0)
    (A : V →ₗ[K] V) (hA : ∀ j, ∀ x ∈ R j, A x ∈ R j) : ∀ i, ∀ x ∈ W, π i (A x) = A (π i x) := by
  intro i x hx
  refine Submodule.iSup_induction R (motive := fun x => π i (A x) = A (π i x)) (hWR hx) ?_ ?_ ?_
  · intro j y hy
    by_cases hij : j = i
    · rw [hij] at hy
      rw [h2 i _ (hA i y hy), h2 i y hy]
    · rw [h3 i j hij _ (hA j y hy), h3 i j hij y hy, map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]
end Formalism.CountingSumsFrames.TO
