-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.range_Lv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:10.030966+00:00
-- url     : https://prove2.me/submissions/bf0b158a-e14a-4c61-90d5-387ae12eb63f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_act_mem
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_E_Lv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution (v : V) : LinearMap.range (Lv G v) = G.gS {v} := by
  have hv : v ∈ G.gS {v} := Submodule.mem_sInf.mpr fun U hU => hU.1 (Set.mem_singleton v)
  have hst : G.Stable (G.gS {v}) := fun a b x hx =>
    Submodule.mem_sInf.mpr fun U hU => hU.2 a b x (Submodule.mem_sInf.mp hx U hU)
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    unfold Lv
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (act_mem G hst w hv)
  · have hR : G.Stable (LinearMap.range (Lv G v)) := fun a b x hx => by
      obtain ⟨c, rfl⟩ := hx
      rw [E_Lv]
      exact LinearMap.mem_range_self _ _
    have hvR : v ∈ LinearMap.range (Lv G v) := ⟨Finsupp.single [] 1, by
      unfold Lv
      rw [Finsupp.linearCombination_single, one_smul]
      rfl⟩
    exact sInf_le (show LinearMap.range (Lv G v) ∈ {U : Submodule K V | {v} ⊆ (U : Set V) ∧ G.Stable U} from
      ⟨Set.singleton_subset_iff.mpr hvR, hR⟩)
end Formalism.CountingSumsFrames.GlX
