-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.Lw_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:45.550072+00:00
-- url     : https://prove2.me/submissions/2887482e-09df-4cc7-b9df-fcb130cac67e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_mem_Lw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_lower
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le

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
theorem _root_.solution {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) : G.Stable (G.Lw v) := by
  let U' : Submodule K V :=
    { carrier := {x | x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v}
      add_mem' := fun {x y} hx hy => ⟨(G.Lw v).add_mem hx.1 hy.1, fun a b => by
        rw [map_add]; exact (G.Lw v).add_mem (hx.2 a b) (hy.2 a b)⟩
      zero_mem' := ⟨(G.Lw v).zero_mem, fun a b => by rw [map_zero]; exact (G.Lw v).zero_mem⟩
      smul_mem' := fun c x hx => ⟨(G.Lw v).smul_mem c hx.1, fun a b => by
        rw [map_smul]; exact (G.Lw v).smul_mem c (hx.2 a b)⟩ }
  have hle : G.Lw v ≤ U' := by
    apply G.Lw_le
    · show v ∈ G.Lw v ∧ ∀ a b, G.E a b v ∈ G.Lw v
      refine ⟨G.mem_Lw v, fun a b => ?_⟩
      rcases lt_trichotomy a b with h | h | h
      · rw [hv.2 a b h]; exact (G.Lw v).zero_mem
      · subst h; rw [G.E_diag_of_isWt hv.1]; exact (G.Lw v).smul_mem _ (G.mem_Lw v)
      · exact G.Lw_lower v h (G.mem_Lw v)
    · intro c d hcd x hx
      have hx' : x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v := hx
      show G.E c d x ∈ G.Lw v ∧ ∀ a b, G.E a b (G.E c d x) ∈ G.Lw v
      refine ⟨G.Lw_lower v hcd hx'.1, fun a b => ?_⟩
      rw [G.comm' a b c d x]
      refine (G.Lw v).add_mem (G.Lw_lower v hcd (hx'.2 a b)) ((G.Lw v).sub_mem ?_ ?_)
      · split_ifs
        · exact hx'.2 a d
        · exact (G.Lw v).zero_mem
      · split_ifs
        · exact hx'.2 c b
        · exact (G.Lw v).zero_mem
  intro a b x hx
  exact (show x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v from hle hx).2 a b
end Formalism.GM.DimensionMonotonicity.GlW
