-- Prove2me | solution 1 for BKAR.Forest.le_pathMinAux_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:50.353558+00:00
-- url     : https://prove2.me/submissions/b23d3f75-0387-4e46-9178-197324fdffeb

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
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
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (s a : ℝ) :
    ∀ γ : List (Edge V),
      s ≤ F.pathMinAux u a γ ↔
        s ≤ a ∧ ∀ e ∈ γ, s ≤ F.paramValue u e
  | [] => by
      simp [pathMinAux]
  | e :: γ => by
      rw [pathMinAux]
      rw [solution F u s (min a (F.paramValue u e)) γ]
      rw [le_min_iff]
      constructor
      · rintro ⟨⟨hsa, hse⟩, htail⟩
        refine ⟨hsa, ?_⟩
        intro e' he'
        rw [List.mem_cons] at he'
        exact he'.elim (fun heq => heq ▸ hse) (htail e')
      · rintro ⟨hsa, hall⟩
        refine ⟨⟨hsa, hall e (by simp)⟩, ?_⟩
        intro e' he'
        exact hall e' (by simp [he'])
end BKAR.Forest
