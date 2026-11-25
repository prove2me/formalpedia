-- Prove2me | solution 1 for Erdos919.exists_superset_aleph1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:19.080593+00:00
-- url     : https://prove2.me/submissions/e2fcb65d-016b-4767-8ea3-bb862ab349ee

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (hV : ℵ₁ ≤ #V) (X : Set V) (hX : #X ≤ ℵ₁) :
    ∃ Y : Set V, X ⊆ Y ∧ #Y = ℵ₁ := by
  obtain ⟨Z, hZ⟩ := le_mk_iff_exists_set.1 hV
  refine ⟨X ∪ Z, subset_union_left, le_antisymm ?_ ?_⟩
  · calc #(X ∪ Z : Set V) ≤ #X + #Z := mk_union_le _ _
      _ ≤ ℵ₁ + ℵ₁ := add_le_add hX hZ.le
      _ = ℵ₁ := add_eq_self (aleph0_le_aleph 1)
  · rw [← hZ]
    exact mk_le_mk_of_subset subset_union_right
end Erdos919
