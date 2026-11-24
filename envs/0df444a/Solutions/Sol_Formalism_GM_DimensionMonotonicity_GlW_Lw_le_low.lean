-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.Lw_le_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.104091+00:00
-- url     : https://prove2.me/submissions/18c2e12a-e4bd-481b-b3c9-e2683dae1526

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_dl_ne_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_E
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_trans
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_antisymm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_lower
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le
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
theorem _root_.solution {la : Fin r → ℤ} {v : V} (hv : G.IsWt la v) :
    G.Lw v ≤ Submodule.span K {v} ⊔ G.Low la := by
  apply G.Lw_le
  · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · intro a b hab x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul]
    apply Submodule.mem_sup_right
    refine (G.Low la).add_mem ((G.Low la).smul_mem c ?_) ?_
    · show ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν (G.E a b v) = 0
      intro ν hν
      rw [G.comp_of_isWt (G.isWt_E hv a b), if_neg]
      rintro rfl
      exact hν ⟨Dle_lower la hab, fun h => dl_ne_zero hab.ne' (by simpa using h)⟩
    · have hz' : ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν z = 0 := hz
      show ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν (G.E a b z) = 0
      intro ν hν
      rw [G.shift]
      by_cases h : Dle (ν - dl a b) la ∧ ν - dl a b ≠ la
      · exfalso
        apply hν
        have hd : Dle ν (ν - dl a b) := by
          have h5 := Dle_lower (ν - dl a b) hab
          rwa [sub_add_cancel] at h5
        refine ⟨Dle_trans hd h.1, fun heq => ?_⟩
        subst heq
        exact h.2 (Dle_antisymm hd h.1).symm
      · rw [hz' _ h, map_zero]
end Formalism.GM.DimensionMonotonicity.GlW
