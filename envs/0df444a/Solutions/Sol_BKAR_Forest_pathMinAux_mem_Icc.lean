-- Prove2me | solution 1 for BKAR.Forest.pathMinAux_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:10.999586+00:00
-- url     : https://prove2.me/submissions/93927495-1642-4186-8859-d16dd3a7f951

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_mem_Icc

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    ∀ {a : ℝ}, 0 ≤ a ∧ a ≤ 1 → ∀ γ : List (Edge V),
      0 ≤ F.pathMinAux u a γ ∧ F.pathMinAux u a γ ≤ 1
  | a, ha, [] => ha
  | a, ha, e :: γ => by
      have he := F.paramValue_mem_Icc u hu e
      have hmin : 0 ≤ min a (F.paramValue u e) ∧
          min a (F.paramValue u e) ≤ 1 :=
        ⟨le_min ha.1 he.1, (min_le_left _ _).trans ha.2⟩
      exact solution F u hu hmin γ
end BKAR.Forest
