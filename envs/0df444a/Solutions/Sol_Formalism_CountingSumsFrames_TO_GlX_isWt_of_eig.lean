-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.isWt_of_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:48.826596+00:00
-- url     : https://prove2.me/submissions/8e641212-c4e2-4f05-8ce4-5a76566ecdca

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
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution {μ : Fin r → ℤ} {z : V} (hz : ∀ c, G.E c c z = ((μ c : ℤ) : K) • z) : G.IsWt μ z := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt
  obtain ⟨S, hS⟩ := G.dec z
  have hkill : ∀ ν, ν ≠ μ → G.comp ν z = 0 := by
    intro ν hne
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have h1 := G.shift c c ν z
    have hdl : Formalism.GM.DimensionMonotonicity.dl c c = (0 : Fin r → ℤ) := by simp [Formalism.GM.DimensionMonotonicity.dl]
    rw [hdl, sub_zero, G.diag c ν z, hz c, map_smul] at h1
    have h2 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) • G.comp ν z = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hc
    exact (smul_eq_zero.mp h2).resolve_left h3
  have hsum := G.sum_comp z S hS
  rw [Finset.sum_eq_single μ (fun ν _ hne => hkill ν hne) (fun hμ => hS μ hμ)] at hsum
  exact hsum
end Formalism.CountingSumsFrames.TO.GlX
