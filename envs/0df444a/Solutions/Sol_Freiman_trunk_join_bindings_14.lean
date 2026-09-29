-- Prove2me | solution 1 for Freiman.trunk_join_bindings_14
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:19.608686+00:00
-- url     : https://prove2.me/submissions/3188b645-ccf8-4b18-a53f-31e3f7cc1d84

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 4000

theorem solution (h0 : trunkBindingBatch 14 0 66) :
    ∀ g ∈ (trunkCatalog.states 14).groups, trunkGroupValid trunkCatalog 14 g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have hilt : i < (trunkCatalog.states 14).groups.length := (List.getElem?_eq_some_iff.mp hi).elim (fun h _ => h)
  exact h0 i (Nat.zero_le _) hilt g hi
