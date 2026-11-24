-- Prove2me | solution 1 for FongoSync.gidSet_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:57.792412+00:00
-- url     : https://prove2.me/submissions/ddfc328e-6588-4cc8-a784-f32b2fd72f11

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
import Theorems.Thm_FongoSync_mem_gidSet
import Theorems.Thm_FongoSync_sorted_gidSet
import Theorems.Thm_FongoSync_eq_of_sorted

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {l₁ l₂ : List Gid} (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    gidSet l₁ = gidSet l₂ :=
  eq_of_sorted (sorted_gidSet l₁) (sorted_gidSet l₂) fun x => by simp [mem_gidSet, same]
end FongoSync
