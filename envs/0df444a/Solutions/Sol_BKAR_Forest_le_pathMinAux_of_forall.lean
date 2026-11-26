-- Prove2me | solution 1 for BKAR.Forest.le_pathMinAux_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:41.963912+00:00
-- url     : https://prove2.me/submissions/420c93d4-6bc8-49f0-9fc3-c6ac237eca8c

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_pathMin_cons
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.Forest.pathMin_cons

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} :
    ∀ {a : ℝ}, s ≤ a → ∀ γ : List (Edge V),
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMinAux u a γ
  | a, ha, [] => fun _ => ha
  | a, ha, e :: γ => by
      intro hγ
      apply solution F u
        (a := min a (F.paramValue u e))
      · exact le_min ha (hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial))
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')
end BKAR.Forest
