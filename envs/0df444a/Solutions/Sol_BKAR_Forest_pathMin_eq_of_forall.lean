-- Prove2me | solution 1 for BKAR.Forest.pathMin_eq_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:11.094056+00:00
-- url     : https://prove2.me/submissions/61a67708-d063-4044-af7b-61b039725595

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMinAux_eq_of_forall
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.Forest.pathMin_cons

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMin u γ = G.pathMin v γ
  | [] => fun _ => rfl
  | e :: γ => by
      intro hγ
      apply pathMinAux_eq_of_forall F G u v
      · exact hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial)
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')
end BKAR.Forest
