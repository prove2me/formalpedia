-- Prove2me | solution 1 for BKAR.Forest.le_pathMin_of_forall_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:45.234795+00:00
-- url     : https://prove2.me/submissions/68ea85ef-ef5b-41b8-9973-c745b07be76f

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
import Theorems.Thm_BKAR_Forest_le_pathMinAux_iff
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs : s ≤ 1) :
    ∀ γ : List (Edge V),
      (∀ e ∈ γ, s ≤ F.paramValue u e) →
        s ≤ F.pathMin u γ
  | [] => fun _ => by
      simpa [pathMin] using hs
  | e :: γ => fun hγ => by
      rw [pathMin_cons]
      exact (le_pathMinAux_iff F u s (F.paramValue u e) γ).mpr
        ⟨hγ e (by simp), fun e' he' => hγ e' (by simp [he'])⟩
end BKAR.Forest
