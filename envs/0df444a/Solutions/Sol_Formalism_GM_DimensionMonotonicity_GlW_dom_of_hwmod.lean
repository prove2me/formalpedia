-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.dom_of_hwmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:37.600142+00:00
-- url     : https://prove2.me/submissions/3544f93d-700b-414a-9ff2-9b2be6476850

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_pow
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_pow_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_sl2
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {U W : Submodule K V} (hU : G.Stable U) (hW : G.Stable W) (hWf : G.FinW W)
    {μ : Fin r → ℤ} {v : V} (hvW : v ∈ W) (hvU : v ∉ U) (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : DomW μ := by
  intro a b hab
  by_contra hlt
  push_neg at hlt
  have hne : a ≠ b := hab.ne
  have key : ∀ k : ℕ, (G.E b a ^ k) v ∉ U := by
    intro k
    induction k with
    | zero => simpa using hvU
    | succ k ih =>
      intro hk
      apply ih
      have h1 := hU a b _ hk
      rw [G.sl2 hne hv k] at h1
      have h2 : (G.E b a ^ (k + 1)) (G.E a b v) ∈ U := G.pow_mem hU b a (k + 1) (hr a b hab)
      have h3 := U.sub_mem h1 h2
      rw [add_sub_cancel_left] at h3
      have hc : (((k + 1 : ℕ) : K) * ((μ a - μ b - k : ℤ) : K)) ≠ 0 := by
        apply mul_ne_zero
        · first
            | exact_mod_cast Nat.succ_ne_zero k
            | exact Nat.cast_add_one_ne_zero k
            | (push_cast; exact Nat.cast_add_one_ne_zero k)
        · have h6 : μ a - μ b - (k : ℤ) ≠ 0 := by omega
          exact_mod_cast h6
      have h4 := U.smul_mem (((k + 1 : ℕ) : K) * ((μ a - μ b - k : ℤ) : K))⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h4
  obtain ⟨S, hS⟩ := hWf
  have hinj : Function.Injective (fun k : ℕ => μ + (k : ℤ) • dl b a) := by
    intro k l hkl
    have h7 := congrFun hkl a
    simp [dl_apply, hne] at h7
    omega
  have hex : ∃ w ∈ Set.range (fun k : ℕ => μ + (k : ℤ) • dl b a), w ∉ S := by
    first
      | exact (Set.infinite_range_of_injective hinj).exists_not_mem_finset S
      | exact (Set.infinite_range_of_injective hinj).exists_notMem_finset S
  obtain ⟨w, ⟨k, rfl⟩, hw⟩ := hex
  have hwt' : G.comp (μ + (k : ℤ) • dl b a) ((G.E b a ^ k) v) = (G.E b a ^ k) v := G.isWt_pow hv b a k
  have hkW : (G.E b a ^ k) v ∈ W := G.pow_mem hW b a k hvW
  have h0 : (G.E b a ^ k) v = 0 := hwt'.symm.trans (hS _ hkW _ hw)
  exact key k (by rw [h0]; exact U.zero_mem)
end Formalism.GM.DimensionMonotonicity.GlW
