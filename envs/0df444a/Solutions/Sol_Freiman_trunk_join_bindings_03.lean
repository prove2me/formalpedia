-- Prove2me | solution 1 for Freiman.trunk_join_bindings_03
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:37:58.974677+00:00
-- url     : https://prove2.me/submissions/a46af349-dbf9-494c-ac85-f884b3b7ebc1

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 3 0 100) (h1 : trunkBindingBatch 3 100 200) (h2 : trunkBindingBatch 3 200 213) :
    ∀ g ∈ (trunkCatalog.states 3).groups, trunkGroupValid trunkCatalog 3 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 3).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  rcases lt_or_ge i 200 with c1 | c1n
  · exact h1 i c0n c1 g hi
  exact h2 i c1n hilt g hi
