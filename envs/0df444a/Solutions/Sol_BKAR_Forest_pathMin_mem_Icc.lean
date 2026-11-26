-- Prove2me | solution 1 for BKAR.Forest.pathMin_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:39.215682+00:00
-- url     : https://prove2.me/submissions/ba11e72b-a198-4684-a010-04b9dabaffd4

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_mem_Icc
import Theorems.Thm_BKAR_Forest_pathMinAux_mem_Icc

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    ∀ γ : List (Edge V), 0 ≤ F.pathMin u γ ∧ F.pathMin u γ ≤ 1
  | [] => ⟨zero_le_one, le_rfl⟩
  | e :: γ => by
      exact F.pathMinAux_mem_Icc u hu (F.paramValue_mem_Icc u hu e) γ
end BKAR.Forest
