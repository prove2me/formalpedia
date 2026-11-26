-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:51.360046+00:00
-- url     : https://prove2.me/submissions/d9880d89-1f82-4edd-900d-70eeea793788

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_EdgeExtension_old_mem


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.extendParam u s ⟨e, h.old_mem he⟩ = u ⟨e, he⟩ := by
  have hne : (⟨e, h.old_mem he⟩ : F'.EdgeParam).val ≠ e₀ := by
    intro heq
    have heq' : e = e₀ := heq
    exact h.new_not_mem (heq' ▸ he)
  rw [extendParam, dif_neg hne]
end BKAR.Forest.EdgeExtension
