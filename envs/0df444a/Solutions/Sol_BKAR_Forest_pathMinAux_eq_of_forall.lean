-- Prove2me | solution 1 for BKAR.Forest.pathMinAux_eq_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:35.6728+00:00
-- url     : https://prove2.me/submissions/50419861-71d7-40a9-b3a0-4feb4b5dc214

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
theorem _root_.solution (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ {a b : ℝ}, a = b → ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMinAux u a γ = G.pathMinAux v b γ
  | a, b, hab, [] => fun _ => hab
  | a, b, hab, e :: γ => by
      intro hγ
      apply solution F G u v
        (a := min a (F.paramValue u e)) (b := min b (G.paramValue v e))
      · rw [hab, hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial)]
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')
end BKAR.Forest
