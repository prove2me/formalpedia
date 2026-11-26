-- Prove2me | solution 1 for BKAR.Forest.paramValue_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:57.995975+00:00
-- url     : https://prove2.me/submissions/b5878750-ed43-4962-ab4a-f93c13cdedc9

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
attribute [local simp] BKAR.Forest.paramValue_of_mem

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.paramValue u e ∧ F.paramValue u e ≤ 1 := by
  by_cases he : e ∈ F.edges
  · rw [paramValue_of_mem F u he]
    exact hu ⟨e, he⟩
  · rw [paramValue, dif_neg he]
    exact ⟨zero_le_one, le_rfl⟩
end BKAR.Forest
