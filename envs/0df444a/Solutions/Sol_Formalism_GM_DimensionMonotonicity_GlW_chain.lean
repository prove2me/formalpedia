-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:52.051864+00:00
-- url     : https://prove2.me/submissions/80909edf-5d64-400b-92de-2a4950413b9a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_raising_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_Cas
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_sup_stable
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
theorem _root_.solution {W V0 : Submodule K V} [FiniteDimensional K W] (hW : G.Stable W) (hWf : G.FinW W)
    (hV0 : G.Stable V0) (hV0W : V0 ≤ W) (c0 : ℤ)
    (H : ∀ U : Submodule K V, G.Stable U → V0 ≤ U → U ≤ W → ∀ μ v, v ∈ W → v ∉ U → G.IsWt μ v →
      (∀ a b, a < b → G.E a b v ∈ U) → casI μ ≠ c0) :
    ∃ cs : List ℤ, (∀ c ∈ cs, c ≠ c0) ∧ ∀ x ∈ W, G.cprod cs x ∈ V0 := by
  suffices hs : ∀ n : ℕ, ∀ U : Submodule K V, G.Stable U → V0 ≤ U → U ≤ W →
      Module.finrank K W - Module.finrank K U ≤ n →
      ∃ cs : List ℤ, (∀ c ∈ cs, c ≠ c0) ∧ ∀ x ∈ W, G.cprod cs x ∈ U from
    hs _ V0 hV0 le_rfl hV0W le_rfl
  intro n
  induction n with
  | zero =>
    intro U hU hVU hUW hn
    refine ⟨[], by simp, fun x hx => ?_⟩
    have h1 : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono hUW
    have hUW' : U = W := Submodule.eq_of_le_of_finrank_le hUW (by omega)
    simpa [cprod, hUW'] using hx
  | succ n ih =>
    intro U hU hVU hUW hn
    by_cases hWU : W ≤ U
    · exact ⟨[], by simp, fun x hx => by simpa [cprod] using hWU hx⟩
    obtain ⟨v, hvW, hvU, μ, hvw, hr⟩ := G.exists_hwmod (G.graded_of hW) (G.raising_of hW) hWf hWU
    let U' := U ⊔ G.gS {v}
    have hgW : G.gS {v} ≤ W := G.gS_le (by simpa using hvW) hW
    have hU' : G.Stable U' := G.sup_stable hU (G.gS_stable _)
    have hU'W : U' ≤ W := sup_le hUW hgW
    have hlt : U < U' := by
      refine lt_of_le_of_ne le_sup_left fun heq => hvU ?_
      rw [heq]; exact Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton v))
    haveI : FiniteDimensional K U' := Submodule.finiteDimensional_of_le hU'W
    have hrk : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt (t := U') hlt
    have hrk2 : Module.finrank K U' ≤ Module.finrank K W := Submodule.finrank_mono hU'W
    obtain ⟨cs, hcs, hx⟩ := ih U' hU' (hVU.trans le_sup_left) hU'W (by omega)
    refine ⟨casI μ :: cs, ?_, fun x hxW => ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst h; exact H U hU hVU hUW μ v hvW hvU hvw hr
      · exact hcs c h
    · rw [cprod_cons]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hx x hxW)
      rw [← hyz, map_add, smul_add, add_sub_add_comm]
      refine U.add_mem (U.sub_mem (G.Cas_mem hU hy) (U.smul_mem _ hy)) ?_
      let Q : Submodule K V := Submodule.comap (G.Cas - ((casI μ : ℤ) : K) • LinearMap.id) U
      have hQ : G.gS {v} ≤ Q := by
        apply G.gS_le
        · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
          simpa [Q] using G.Cas_hwmod hU hvw hr
        · intro a b y hy
          simp only [Q, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
          rw [← G.E_Cas, ← map_smul, ← map_sub]; exact hU a b _ hy
      simpa [Q] using hQ hz
end Formalism.GM.DimensionMonotonicity.GlW
