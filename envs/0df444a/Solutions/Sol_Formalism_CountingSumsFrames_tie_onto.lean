-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tie_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:22:18.622731+00:00
-- url     : https://prove2.me/submissions/011d834b-7193-4885-95fc-fe9e9999442e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_small_onto
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_comap
import Theorems.Thm_Formalism_CountingSumsFrames_pol_comap
import Theorems.Thm_Formalism_CountingSumsFrames_exists_small
import Theorems.Thm_Formalism_CountingSumsFrames_Y_min_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (μ : Fin r → ℤ)
    {v : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hv : v ∈ GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr) :
    ∃ f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      T.Ffull p (LL.setTies T n) i ρ (n i) f = v := by
  classical
  have hK := hK_of_adm LL T hadm i
  obtain ⟨hvH, hvC⟩ := Submodule.mem_inf.mp hv
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hvC
  have hvH' : (GA p LL (T.pos i + 1 + 1)).IsHW μ v := hvH
  obtain ⟨v', rfl⟩ := exists_small LL T hadm i n hvP
  have hinj := inclusion_prodMap_injective (N := N) (r := r) hK
  have hA : ∀ k, v' ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (min (T.J k) (T.pos i + 1))
      (T.thrUpTo i k) := by
    intro k
    by_cases hk : T.J k ≤ T.pos i + 1
    · have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [min_eq_left hk, e2]
      exact ycond_comap _ LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a) hinj
        (T.J k) (T.thr k) (wv_compat LL T hadm i n (n i) (T.J k)) h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, ycond_top]; exact Submodule.mem_top
  have hB : IsWeightedHomogeneous (wv (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (T.pos i + 1 + 1)) v' μ := by
    intro m' hm'
    have h1 : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1))
        (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v') μ := by
      have h0 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ _ = _ := hvH'.1
      rw [← h0]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have h2 : coeff (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m')
        (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v') ≠ 0 := by
      rw [coeff_rename_mapDomain _ hinj]; exact hm'
    have h3 := h1 h2
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h3
  have hC : ∀ a b, a < b → glAct p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (T.pos i + 1 + 1) a b v' = 0 := by
    intro a b hab
    apply rename_injective _ hinj
    rw [glAct_rename _ LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a), map_zero]
    exact hvH'.2 a b hab
  obtain ⟨f, hf, hfv⟩ := small_onto ((LL.setTies T n).takeD (T.pos i + 1)) ρ hρ (n i) hS
    (fun k => min (T.J k) (T.pos i + 1)) (T.thrUpTo i) (fun k => min_le_right _ _) μ v'
    (pol_comap LL T hadm i n hvP) hA hB hC
  refine ⟨f, ?_, ?_⟩
  · unfold MMw at hf ⊢
    rwa [Y_min_eq LL T hadm i] at hf
  · rw [Ffull_eq, hfv]
end Formalism.CountingSumsFrames
