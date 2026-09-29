-- Prove2me | solution 1 for Freiman.trunk_join_bindings_11
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:13.976488+00:00
-- url     : https://prove2.me/submissions/6b667ab2-aab7-4559-81b8-1bdddef6836e

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 11 0 100) (h1 : trunkBindingBatch 11 100 121) :
    ∀ g ∈ (trunkCatalog.states 11).groups, trunkGroupValid trunkCatalog 11 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 11).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  exact h1 i c0n hilt g hi
