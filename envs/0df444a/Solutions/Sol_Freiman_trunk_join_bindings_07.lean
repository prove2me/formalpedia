-- Prove2me | solution 1 for Freiman.trunk_join_bindings_07
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:06.681476+00:00
-- url     : https://prove2.me/submissions/2476b8f9-7cd2-49b1-9695-cc65cf9a39a3

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 7 0 100) (h1 : trunkBindingBatch 7 100 200) (h2 : trunkBindingBatch 7 200 207) :
    ∀ g ∈ (trunkCatalog.states 7).groups, trunkGroupValid trunkCatalog 7 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 7).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  rcases lt_or_ge i 200 with c1 | c1n
  · exact h1 i c0n c1 g hi
  exact h2 i c1n hilt g hi
