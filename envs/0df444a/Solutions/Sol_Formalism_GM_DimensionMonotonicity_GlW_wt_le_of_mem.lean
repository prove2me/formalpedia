-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.wt_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:53.246704+00:00
-- url     : https://prove2.me/submissions/e83b37f0-0d17-4634-abe3-2faf091f22fe

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_refl
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le_Lw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le_low

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
theorem _root_.solution {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {x : V} (hx : x ∈ G.gS {v})
    {ν : Fin r → ℤ} (h : G.comp ν x ≠ 0) : Dle ν la := by
  have hx' : x ∈ Submodule.span K {v} ⊔ G.Low la := G.Lw_le_low hv.1 (G.gS_le_Lw hv hx)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  by_contra hle
  apply h
  have hz' : ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν z = 0 := hz
  have hne : ν ≠ la := fun e => hle (by rw [e]; exact Dle_refl la)
  rw [map_add, map_smul, G.comp_of_isWt hv.1, if_neg hne, smul_zero, zero_add]
  exact hz' ν (fun h' => hle h'.1)
end Formalism.GM.DimensionMonotonicity.GlW
