-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.paramValue_extend_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:31.990539+00:00
-- url     : https://prove2.me/submissions/aadef558-08fc-4de5-8a56-d9c788079581

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_EdgeExtension_le_extendParam
attribute [local simp] BKAR.Forest.paramValue_of_mem

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
    (hu : ∀ e : F.EdgeParam, s ≤ u e) {e : Edge V}
    (he : e ∈ F'.edges) :
    s ≤ F'.paramValue (h.extendParam u s) e := by
  rw [paramValue_of_mem F' (h.extendParam u s) he]
  exact h.le_extendParam u hu ⟨e, he⟩
end BKAR.Forest.EdgeExtension
