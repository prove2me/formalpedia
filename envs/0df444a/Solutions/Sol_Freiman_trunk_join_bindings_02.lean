-- Prove2me | solution 1 for Freiman.trunk_join_bindings_02
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:37:57.093904+00:00
-- url     : https://prove2.me/submissions/3a07e754-6de4-4915-aa84-02a17e1394c5

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 2 0 100) (h1 : trunkBindingBatch 2 100 184) :
    ∀ g ∈ (trunkCatalog.states 2).groups, trunkGroupValid trunkCatalog 2 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 2).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  rcases lt_or_ge i 100 with c0 | c0n
  · exact h0 i (Nat.zero_le _) c0 g hi
  exact h1 i c0n hilt g hi
