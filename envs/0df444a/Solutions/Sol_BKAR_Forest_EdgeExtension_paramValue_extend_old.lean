-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.paramValue_extend_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:16.282812+00:00
-- url     : https://prove2.me/submissions/a38d4fe8-476e-4a87-878b-176134d75db2

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_old
import Theorems.Thm_BKAR_Forest_EdgeExtension_old_mem

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
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    F'.paramValue (h.extendParam u s) e = F.paramValue u e := by
  rw [paramValue_of_mem F' (h.extendParam u s) (h.old_mem he),
    h.extendParam_old u s he, paramValue_of_mem F u he]
end BKAR.Forest.EdgeExtension
