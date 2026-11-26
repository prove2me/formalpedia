-- Prove2me | solution 1 for BKAR.Forest.pathMin_le_of_mem_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:18.238247+00:00
-- url     : https://prove2.me/submissions/452326ed-f9e0-4d00-a69f-c509c798ade8

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMinAux_le_seed
import Theorems.Thm_BKAR_Forest_pathMinAux_le_of_mem_eq

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMin u γ ≤ s
  | [], hmem => by
      cases hmem
  | e :: γ, hmem => by
      intro heq
      by_cases hhead : e = e₀
      · have hseed : F.paramValue u e ≤ s := by
          rw [hhead, heq]
        exact (F.pathMinAux_le_seed u (F.paramValue u e) γ).trans hseed
      · have htail : e₀ ∈ γ := by
          rw [List.mem_cons] at hmem
          exact hmem.elim (fun h => False.elim (hhead h.symm)) id
        exact pathMinAux_le_of_mem_eq F u γ htail heq
end BKAR.Forest
