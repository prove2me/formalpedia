-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.exists_hwmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:37.642975+00:00
-- url     : https://prove2.me/submissions/f16c5573-07ff-4500-9b28-7388e601a767

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_comp
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_E
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_sum_comp_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_ht_add_dl

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
theorem _root_.solution {W U : Submodule K V} (hWg : G.Graded W) (hWr : G.Raising W) (hWf : G.FinW W)
    (h : ¬ W ≤ U) : ∃ v ∈ W, v ∉ U ∧ ∃ μ, G.IsWt μ v ∧ ∀ a b, a < b → G.E a b v ∈ U := by
  classical
  obtain ⟨S, hS⟩ := hWf
  obtain ⟨x, hxW, hxU⟩ := SetLike.not_le_iff_exists.mp h
  have hex : ∃ μ, G.comp μ x ∉ U := by
    by_contra hcon
    push_neg at hcon
    apply hxU
    rw [G.sum_comp_eq x (fun μ hμ => hS x hxW μ hμ)]
    exact Submodule.sum_mem _ fun μ _ => hcon μ
  obtain ⟨μ0, hμ0⟩ := hex
  have hμ0S : μ0 ∈ S := by
    by_contra hn
    exact hμ0 (by rw [hS x hxW μ0 hn]; exact U.zero_mem)
  have hTne : (S.filter (fun μ => ∃ v ∈ W, v ∉ U ∧ G.IsWt μ v)).Nonempty :=
    ⟨μ0, Finset.mem_filter.mpr ⟨hμ0S, G.comp μ0 x, hWg μ0 x hxW, hμ0, G.isWt_comp μ0 x⟩⟩
  obtain ⟨μ, hμT, hmax⟩ := Finset.exists_max_image _ ht hTne
  obtain ⟨_, v, hvW, hvU, hv⟩ := Finset.mem_filter.mp hμT
  refine ⟨v, hvW, hvU, μ, hv, fun a b hab => ?_⟩
  by_contra hE
  have hw := G.isWt_E hv a b
  have hWE : G.E a b v ∈ W := hWr a b hab v hvW
  have hS' : μ + dl a b ∈ S := by
    by_contra hn
    apply hE
    have h0 : G.E a b v = 0 :=
      (show G.comp (μ + dl a b) (G.E a b v) = G.E a b v from hw).symm.trans (hS _ hWE _ hn)
    rw [h0]
    exact U.zero_mem
  have hle := hmax (μ + dl a b) (Finset.mem_filter.mpr ⟨hS', G.E a b v, hWE, hE, hw⟩)
  rw [ht_add_dl] at hle
  have hab' : (a : ℕ) < b := hab
  omega
end Formalism.GM.DimensionMonotonicity.GlW
