-- Prove2me | solution 1 for Freiman.trunk_join_bindings_13
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:17.714291+00:00
-- url     : https://prove2.me/submissions/33fd9dc6-f5d0-40c6-8a5f-c7a88ee0d27e

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 13 0 100) (h1 : trunkBindingBatch 13 100 173) :
    ∀ g ∈ (trunkCatalog.states 13).groups, trunkGroupValid trunkCatalog 13 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 13).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  exact h1 i c0n hilt g hi
