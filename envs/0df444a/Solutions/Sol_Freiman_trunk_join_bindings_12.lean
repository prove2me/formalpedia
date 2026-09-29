-- Prove2me | solution 1 for Freiman.trunk_join_bindings_12
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:15.872123+00:00
-- url     : https://prove2.me/submissions/f1f6d56d-709c-4285-92c9-7f498f6dcbab

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 12 0 100) (h1 : trunkBindingBatch 12 100 178) :
    ∀ g ∈ (trunkCatalog.states 12).groups, trunkGroupValid trunkCatalog 12 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 12).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  exact h1 i c0n hilt g hi
