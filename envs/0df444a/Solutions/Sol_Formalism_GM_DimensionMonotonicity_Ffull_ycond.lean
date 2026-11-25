-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Ffull_ycond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:49:13.28784+00:00
-- url     : https://prove2.me/submissions/fdc361c6-0a75-4523-9abe-517a16d18f7b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_map
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
import Theorems.Thm_Formalism_GM_extendWeightBounded
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (ρ : Fin r) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (k : Fin T.q) (hk : T.J k ≤ T.pos i + 1) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ YCond p LL (T.J k) (T.thr k) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hY : f ∈ Y p LLK T.J (T.thrUpTo i) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hY).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hY' : f ∈ Y p LLK J' (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hP, Submodule.mem_iInf _ |>.mpr fun k' => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hY).2 k'
    by_cases hk' : T.J k' ≤ T.pos i + 1
    · simpa [J', min_eq_left hk'] using this
    · have ht : T.thrUpTo i k' = ⊤ := by simp [TieData.thrUpTo, hk']
      rw [ht, ycond_top]; exact Submodule.mem_top
  have hF := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hP).mp hY'
  have hF2 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 k
  have e1 : J' k = T.J k := min_eq_left hk
  have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
  rw [e1, e2] at hF2
  rw [Ffull_eq]
  refine Formalism.GM.FrozenVariableComponents.ycond_map p (LLK.snoc (n i)) LL (T.J k) (T.J k) (T.thr k)
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap
    (fun c d G => glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) (T.J k) c d G) ?_ _ hF2
  intro G m hm
  rw [AlgHom.toLinearMap_apply, support_rename_of_injective (inclusion_prodMap_injective (r := r) hK), Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  refine ⟨m0, hm0, ?_⟩
  rw [← weight_wv, ← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i)]
end Formalism.GM.DimensionMonotonicity
