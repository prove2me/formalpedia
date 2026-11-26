-- Prove2me | solution 1 for BKAR.Forest.pathMinAux_le_of_mem_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:43.616021+00:00
-- url     : https://prove2.me/submissions/67e9d517-3537-42c5-bb34-a18228b3fea0

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMinAux_le_seed

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {a : ℝ} (γ : List (Edge V)), e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMinAux u a γ ≤ s
  | a, [], hmem => by
      cases hmem
  | a, e :: γ, hmem => by
      intro heq
      by_cases hhead : e = e₀
      · have hseed : min a (F.paramValue u e) ≤ s := by
          rw [hhead, heq]
          exact min_le_right _ _
        exact (F.pathMinAux_le_seed u (min a (F.paramValue u e)) γ).trans hseed
      · have htail : e₀ ∈ γ := by
          rw [List.mem_cons] at hmem
          exact hmem.elim (fun h => False.elim (hhead h.symm)) id
        exact solution F u γ htail heq
end BKAR.Forest
