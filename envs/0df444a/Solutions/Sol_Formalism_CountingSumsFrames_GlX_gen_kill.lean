-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.gen_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:10.253376+00:00
-- url     : https://prove2.me/submissions/32c209c7-9e14-48d0-93dd-c2645c029b82

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_cprod_kill
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_mem_qlist
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_trans
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cas_lt
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem


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
theorem _root_.solution {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) (hvW : v ∈ W)
    (hv0 : v ≠ 0) {μ ν : Fin r → ℤ} (hμ : DomW μ) (hle : Dle μ ν) (hne : Dle ν la → la ≠ μ) :
    ∀ x ∈ G.gS {v}, G.cprod (qlist S (GlW.casI μ)) (G.comp ν x) = 0 := by
  intro x hx
  have hy : G.comp ν x ∈ G.gS {v} := G.graded_of (G.gS_stable _) ν x hx
  by_cases h0 : G.comp ν x = 0
  · rw [h0, map_zero]
  have hνla : Dle ν la := G.wt_le_of_mem hv hx h0
  have hla : DomW la := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ hvW (by rwa [Submodule.mem_bot])
      hv.1 (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
  have hlt := cas_lt hμ hla (Dle_trans hle hνla) (hne hνla).symm
  have hlaS : la ∈ S := by
    by_contra hn
    exact hv0 (by have := hS v hvW la hn; rwa [hv.1] at this)
  exact cprod_kill G (G.Cas_gS hv hy) _ (mem_qlist hlaS hlt.ne')
end Formalism.CountingSumsFrames.GlX
