-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.hw_is_Ffull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:48:57.16456+00:00
-- url     : https://prove2.me/submissions/731463f6-ca20-4be6-883a-25eff911570c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_of_polLz
import Theorems.Thm_Formalism_CountingSumsFrames_TO_whc_keep
import Theorems.Thm_Formalism_CountingSumsFrames_TO_wtsp_iff
import Theorems.Thm_Formalism_CountingSumsFrames_TO_deg_compat
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ycond_pull
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_norm
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_wh
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freeze_gen
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
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
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
import Theorems.Thm_Formalism_GM_extendBijOn
import Theorems.Thm_Formalism_GM_extendWeightBounded
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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (μ : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hv : v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr)
    (hw : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v) (hint : v ∈ IntPol p (Fin N × Fin r)) :
    ∃ f ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      v = T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  let ι : Fin (T.pos i + 1 + 1) × Fin r → Fin N × Fin r := fun x => (ιF N (T.pos i + 1) x.1, x.2)
  have hι : Function.Injective ι := inclusion_prodMap_injective (r := r) hK
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hv
  have hvF := isF_of_polLz _ _ hvP
  obtain ⟨F, hF⟩ : ∃ F, rename ι F = v := by
    apply exists_rename_eq_of_vars_subset_range v ι hι
    intro x hx
    rw [Finset.mem_coe, mem_vars] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    have hlt : (x.1 : ℕ) < T.pos i + 1 + 1 := hvF m hm x (Finsupp.mem_support_iff.mp hxm)
    exact ⟨(⟨x.1, hlt⟩, x.2), Prod.ext (Fin.ext (ιF_val hK _)) rfl⟩
  have hsupp : ∀ m ∈ F.support, Finsupp.mapDomain ι m ∈ v.support := by
    intro m hm; rw [← hF, support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
  have hFP : F ∈ Pol p r (LLK.snoc (n i)) := by
    rw [Pol, mem_restrictSupport_iff]
    intro m hm a
    have h1 : MultiDeg (Lz (LL.setTies T n) (T.pos i + 1 + 1)) (Finsupp.mapDomain ι m) :=
      ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hvP) (Finset.mem_coe.mpr (hsupp m hm))
    have h2 := h1 (ιF N (T.pos i + 1) a)
    have h3 : ∀ c, Finsupp.mapDomain ι m (ιF N (T.pos i + 1) a, c) = m (a, c) :=
      fun c => Finsupp.mapDomain_apply hι m (a, c)
    simp only [h3] at h2
    rw [h2]
    simp only [Lz]
    rw [if_pos (by rw [ιF_val hK]; exact a.isLt), deg_compat LL T hadm i n]
  have hFI : F ∈ IntPol p (Fin (T.pos i + 1 + 1) × Fin r) := mem_intPol_of_norm _ fun m => by
    have := Formalism.CountingSumsFrames.intPol_norm v hint (Finsupp.mapDomain ι m)
    rwa [← hF, coeff_rename_mapDomain ι hι] at this
  have hgl : ∀ J c d, rename ι (glAct p (LLK.snoc (n i)) J c d F) = glAct p LL J c d v := by
    intro J c d
    rw [← hF]
    exact glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) J c d F
  have hraise : ∀ a b, a < b → glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b F = 0 := by
    intro a b hab
    apply rename_injective ι hι
    rw [hgl, map_zero]
    exact hw.2 a b hab
  have hinv : IsFrozenInv p LLK ρ (n i) F := fun c hc => hraise c ρ (Fin.lt_def.mpr (by
    have := c.isLt
    have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    omega))
  obtain ⟨f, hfZ, hfF⟩ := (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).2 F
    (Submodule.mem_inf.mpr ⟨hFP, hFI⟩) hinv
  have hfP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hfZ).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hFY : freeze p LLK ρ (n i) f ∈ Y p (LLK.snoc (n i)) J' (T.thrUpTo i) := by
    rw [hfF]
    refine Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    by_cases hk : T.J k ≤ T.pos i + 1
    · have e1 : J' k = T.J k := min_eq_left hk
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [e1, e2]
      apply ycond_pull LL T hadm i n
      have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      rw [← hF] at h1
      exact h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  have hfY' := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hfP).mpr hFY
  have hfY : f ∈ Y p LLK T.J (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hfP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hfY').2 k
    by_cases hk : T.J k ≤ T.pos i + 1
    · simpa [J', min_eq_left hk] using h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

  set w : Fin r → ℤ := μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1 with hwd
  have hvW : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1)) v μ := by
    have h1 := weightedHomogeneousComponent_isWeightedHomogeneous (R := ℚ_[p]) (w := wv LL (T.pos i + 1 + 1)) μ v
    have h2 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ v = v := hw.1
    rwa [h2] at h1
  have hFw : IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) F μ := by
    intro m hm
    have h1 := hvW (mem_support_iff.mp (hsupp m (mem_support_iff.mpr hm)))
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h1
  have hcP : ∀ w', weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f ∈ Pol p r LLK := by
    intro w'
    rw [pol_iff] at hfP ⊢
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (whc_keep _ _ w' _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP))
  have hcW : ∀ w', IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1))
      (freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f))
      (w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1) := fun w' =>
    freeze_wh LLK ρ (n i) hS w' _ (hcP w')
      ((wtsp_iff LLK (T.pos i + 1) w' _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous w' f))
  have hcomp : f = weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f := by
    obtain ⟨S, hS0⟩ := (GA p LLK (T.pos i + 1)).dec f
    have hS' : ∀ μ' ∉ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = 0 := hS0
    have hsum : ∑ μ' ∈ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = f :=
      (GA p LLK (T.pos i + 1)).sum_comp f S hS0
    have hfr : freeze p LLK ρ (n i) f =
        ∑ w' ∈ S, freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f) := by
      conv_lhs => rw [← hsum]
      simp only [freeze, map_sum, Finset.mul_sum]
    have h5 : F = freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f) := by
      have h6 : weightedHomogeneousComponent (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) μ F = F := by
        rw [weightedHomogeneousComponent_of_mem hFw, if_pos rfl]
      rw [← h6, ← hfF, hfr, map_sum]
      simp only [weightedHomogeneousComponent_of_mem (hcW _)]
      have hiff : ∀ w', μ = w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1 ↔ w' = w := by
        intro w'; rw [hwd]; constructor
        · intro h; rw [h]; abel
        · intro h; rw [h]; abel
      simp only [hiff]
      rw [Finset.sum_ite_eq' S w]
      split_ifs with hwS
      · rfl
      · rw [hS' w hwS, freeze_zero]
    exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 f hfP _ (hcP w) (by rw [hfF, ← h5])
  have hfW : f ∈ WtSpC p LLK (T.pos i + 1) univ w := by
    rw [wtsp_iff, hcomp]
    exact weightedHomogeneousComponent_isWeightedHomogeneous w f
  have hfH : f ∈ HWC p LLK (T.pos i + 1) (univ.erase ρ) w := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [WtSpC, mem_restrictSupport_iff] at hfW ⊢
      intro m hm c _
      exact hfW hm c (mem_univ c)
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b hab
      have ha : a ≠ ρ := (Finset.mem_erase.mp hab.1).1
      have hb : b ≠ ρ := (Finset.mem_erase.mp hab.2.1).1
      have h1 := glAct_freeze_gen LLK (n i) ρ a b ha hb f
      rw [hfF, hraise a b hab.2.2] at h1
      exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 _
        (Formalism.GM.DimensionMonotonicity.glAct_pol LLK LLK (T.pos i + 1) a b hfP) 0 (Submodule.zero_mem _) (by rw [← h1, freeze_zero])
  refine ⟨f, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfY, hfH⟩, hfW⟩,
    (Submodule.mem_inf.mp hfZ).2⟩, ?_⟩
  rw [Ffull_eq, hfF]
  exact hF.symm
end Formalism.CountingSumsFrames.TO
