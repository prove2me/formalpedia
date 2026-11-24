-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.hw_in_gS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:18.400261+00:00
-- url     : https://prove2.me/submissions/4bc4f33d-e554-4cd1-84c1-12fe4d02d25b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cas_lt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_top_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {W : Submodule K V} (hW : G.Stable W)
    (hWf : G.FinW W) (hvW : v ∈ W) {x : V} (hx : x ∈ G.gS {v}) {μ : Fin r → ℤ} (hxw : G.IsHW μ x)
    (hx0 : x ≠ 0) : μ = la ∧ ∃ c : K, x = c • v := by
  have hx1 : G.comp μ x = x := hxw.1
  have hdle : Dle μ la := G.wt_le_of_mem hv hx (by rw [hx1]; exact hx0)
  by_cases hμ : μ = la
  · subst hμ
    refine ⟨rfl, ?_⟩
    obtain ⟨c, hc⟩ := G.comp_top_of_mem hv hx
    exact ⟨c, by rw [← hc, hx1]⟩
  · exfalso
    have hv0 : v ≠ 0 := by
      rintro rfl
      apply hx0
      have h8 : G.gS {(0 : V)} ≤ ⊥ :=
        G.gS_le (Set.singleton_subset_iff.mpr (Submodule.zero_mem _)) G.bot_stable
      exact (Submodule.mem_bot K).mp (h8 hx)
    have hxW : x ∈ W := G.gS_le (Set.singleton_subset_iff.mpr hvW) hW hx
    have hdomla : DomW la := G.dom_of_hwmod G.bot_stable hW hWf hvW (by rwa [Submodule.mem_bot]) hv.1
      (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
    have hdomμ : DomW μ := G.dom_of_hwmod G.bot_stable hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1
      (fun a b h => by rw [hxw.2 a b h]; exact Submodule.zero_mem _)
    have hlt := cas_lt hdomμ hdomla hdle hμ
    have h1 := G.Cas_gS hv hx
    have h2 : G.Cas x = ((casI μ : ℤ) : K) • x := by
      have h0 := G.Cas_hwmod G.bot_stable hxw.1 (fun a b h => by rw [hxw.2 a b h]; exact Submodule.zero_mem _)
      rw [Submodule.mem_bot] at h0
      exact sub_eq_zero.mp h0
    rw [h1] at h2
    have h3 : (((casI la : ℤ) : K) - ((casI μ : ℤ) : K)) • x = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · rw [sub_eq_zero] at h4
      have h9 : casI la = casI μ := by exact_mod_cast h4
      omega
    · exact hx0 h4
end Formalism.GM.DimensionMonotonicity.GlW
