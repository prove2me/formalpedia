-- Prove2me | solution 1 for Formalism.CountingSumsFrames.small_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:49:02.026735+00:00
-- url     : https://prove2.me/submissions/42ec63ff-3889-406a-b112-6ab2a6ff1fbd

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_freeze_surj
import Theorems.Thm_Formalism_CountingSumsFrames_wt_ext
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freeze_gen
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
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
import Theorems.Thm_Formalism_GM_extendBijOn
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LK : Letters K) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : ℕ) (hS : LK.total ≤ n)
    {q : ℕ} (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ K) (μ : Fin r → ℤ)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFP : F ∈ Pol p r (LK.snoc n))
    (hFY : ∀ k, F ∈ YCond p (LK.snoc n) (J k) (Mt k))
    (hFw : IsWeightedHomogeneous (wv (LK.snoc n) (K + 1)) F μ)
    (hFr : ∀ a b, a < b → glAct p (LK.snoc n) (K + 1) a b F = 0) :
    ∃ f, f ∈ MMw p LK J Mt ρ (μ + ((n : ℕ) : ℤ) • Pi.single ρ 1) ∧ freeze p LK ρ n f = F := by
  classical
  have hlt : ∀ c : Fin r, c ≠ ρ → c < ρ := by
    intro c hc
    have h1 := c.isLt
    have h2 : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    show (c : ℕ) < ρ
    omega
  obtain ⟨f, hfP, hfF, hco⟩ := freeze_surj LK ρ n hS F hFP (fun c hc => hFr c ρ (hlt c hc))
  refine ⟨f, ?_, hfF⟩
  have hW : f ∈ WtSpC p LK K univ (μ + ((n : ℕ) : ℤ) • Pi.single ρ 1) := by
    rw [WtSpC, mem_restrictSupport_iff]
    intro m' hm' c _
    rw [Finset.mem_coe, mem_support_iff, hco] at hm'
    have h1 := congrFun (hFw hm') c
    rw [weight_wv, wt_ext] at h1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at h1 ⊢ <;> simp at h1 ⊢ <;> omega
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, hW⟩
  · refine (Formalism.GM.extendWeightBounded p K r LK ρ n J Mt hS hJ f hfP).mpr ?_
    rw [hfF]
    exact Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr hFY⟩
  · rw [WtSpC, mem_restrictSupport_iff] at hW ⊢
    intro m' hm' c _
    exact hW hm' c (Finset.mem_univ c)
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    rintro a b ⟨ha, hb, hab⟩
    have ha' := Finset.ne_of_mem_erase ha
    have hb' := Finset.ne_of_mem_erase hb
    have h1 := glAct_freeze_gen LK n ρ a b ha' hb' f
    rw [hfF, hFr a b hab] at h1
    exact (Formalism.GM.extendBijOn p K r LK ρ n hS).1 _ (glAct_pol LK LK K a b hfP) 0 (Submodule.zero_mem _)
      (by rw [← h1, freeze_zero])
end Formalism.CountingSumsFrames
