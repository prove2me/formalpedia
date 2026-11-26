-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.le_extendParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:56.865008+00:00
-- url     : https://prove2.me/submissions/f76e172b-d0ee-4f88-b9d7-ccc6daecdf7b

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) (e : F'.EdgeParam) :
    s ≤ h.extendParam u s e := by
  by_cases he : e.val = e₀
  · rw [extendParam, dif_pos he]
  · rw [extendParam, dif_neg he]
    exact hu ⟨e.val, h.mem_old_of_mem_of_ne e.property he⟩
end BKAR.Forest.EdgeExtension
