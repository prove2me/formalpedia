-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:47.770426+00:00
-- url     : https://prove2.me/submissions/2e769827-4dae-4d29-9d55-b71ad5a3f8a9

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem


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
    h.extendParam u s ⟨e₀, h.new_mem⟩ = s := by
  rw [extendParam, dif_pos rfl]
end BKAR.Forest.EdgeExtension
