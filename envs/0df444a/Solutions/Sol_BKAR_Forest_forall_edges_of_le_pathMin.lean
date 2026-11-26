-- Prove2me | solution 1 for BKAR.Forest.forall_edges_of_le_pathMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:02.130441+00:00
-- url     : https://prove2.me/submissions/95a908fe-fc91-4325-b038-87e9d566df0e

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
import Theorems.Thm_BKAR_Forest_le_pathMinAux_iff
import Theorems.Thm_BKAR_Forest_pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_cons



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} :
    ∀ γ : List (Edge V),
      s ≤ F.pathMin u γ →
        ∀ e ∈ γ, s ≤ F.paramValue u e
  | [] => fun _ e he => by cases he
  | e :: γ => fun hmin e' he' => by
      rw [pathMin_cons] at hmin
      have hall :=
        (le_pathMinAux_iff F u s (F.paramValue u e) γ).mp hmin
      rw [List.mem_cons] at he'
      exact he'.elim (fun heq => heq ▸ hall.1) (hall.2 e')
end BKAR.Forest
