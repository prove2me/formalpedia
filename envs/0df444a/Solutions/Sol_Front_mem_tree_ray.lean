-- Prove2me | solution 1 for Front.mem_tree_ray
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:01.742557+00:00
-- url     : https://prove2.me/submissions/9243fb3b-1f8a-4489-9876-5014c808bfe2

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
open Front
variable {F : Set (List ℕ)}
namespace Front
theorem _root_.solution {a : ℕ} {t : List ℕ} : t ∈ tree (ray F a) ↔ a :: t ∈ tree F := by
  constructor
  · rintro ⟨u, hu, hpre⟩
    exact ⟨a :: u, hu, (List.prefix_cons_inj a).mpr hpre⟩
  · rintro ⟨w, hw, hpre⟩
    obtain ⟨v, rfl⟩ := hpre
    exact ⟨t ++ v, hw, List.prefix_append t v⟩
end Front
