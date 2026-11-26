-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.paramValue_extend_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:23.882115+00:00
-- url     : https://prove2.me/submissions/bedeef45-6084-4f7d-b32a-e08f49305361

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_new
import Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem

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
    (u : F.EdgeParam → ℝ) (s : ℝ) :
    F'.paramValue (h.extendParam u s) e₀ = s := by
  rw [paramValue_of_mem F' (h.extendParam u s) h.new_mem,
    h.extendParam_new u s]
end BKAR.Forest.EdgeExtension
