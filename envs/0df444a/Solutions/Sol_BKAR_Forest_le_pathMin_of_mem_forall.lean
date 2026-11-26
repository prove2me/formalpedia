-- Prove2me | solution 1 for BKAR.Forest.le_pathMin_of_mem_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:05.99397+00:00
-- url     : https://prove2.me/submissions/0450f548-ac46-4219-b960-e38666980148

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_le_pathMinAux_of_forall
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
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMin u γ
  | [], hmem => by
      cases hmem
  | e :: γ, _ => by
      intro hγ
      exact F.le_pathMinAux_of_forall u
        (hγ e (by simp only [List.mem_cons, true_or])) γ
        (fun e' he' => hγ e' (by simp only [List.mem_cons, he', or_true]))
end BKAR.Forest
