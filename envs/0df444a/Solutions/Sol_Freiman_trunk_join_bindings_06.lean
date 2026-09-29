-- Prove2me | solution 1 for Freiman.trunk_join_bindings_06
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:04.8461+00:00
-- url     : https://prove2.me/submissions/c6ac3d39-4f4f-473d-8ea8-66c9ad90363c

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 6 0 100) (h1 : trunkBindingBatch 6 100 185) :
    ∀ g ∈ (trunkCatalog.states 6).groups, trunkGroupValid trunkCatalog 6 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 6).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  exact h1 i c0n hilt g hi
