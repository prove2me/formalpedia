-- Prove2me | solution 1 for Freiman.trunk_join_bindings_04
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:00.794317+00:00
-- url     : https://prove2.me/submissions/4591456e-d443-4dad-a762-93054e58b8ca

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 4 0 100) (h1 : trunkBindingBatch 4 100 200) (h2 : trunkBindingBatch 4 200 300) (h3 : trunkBindingBatch 4 300 400) (h4 : trunkBindingBatch 4 400 416) :
    ∀ g ∈ (trunkCatalog.states 4).groups, trunkGroupValid trunkCatalog 4 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 4).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  rcases lt_or_ge i 200 with c1 | c1n
  · exact h1 i c0n c1 g hi
  rcases lt_or_ge i 300 with c2 | c2n
  · exact h2 i c1n c2 g hi
  rcases lt_or_ge i 400 with c3 | c3n
  · exact h3 i c2n c3 g hi
  exact h4 i c3n hilt g hi
