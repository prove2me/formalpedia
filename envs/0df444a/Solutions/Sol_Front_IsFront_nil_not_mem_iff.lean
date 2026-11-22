-- Prove2me | solution 1 for Front.IsFront.nil_not_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:55.357442+00:00
-- url     : https://prove2.me/submissions/72e23dce-84f3-4054-9d9e-15a82609b5d0

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Theorems.Thm_Front_isInit_nil
attribute [local simp] Front.isInit_nil



set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
open Front
variable {F : Set (List ℕ)}
namespace Front
namespace IsFront
theorem _root_.solution (hF : IsFront F M) : [] ∉ F ↔ F ≠ {[]} := by
  constructor
  · intro h heq; exact h (by simp [heq])
  · intro hne hnil
    apply hne
    ext t
    simp only [Set.mem_singleton_iff]
    exact ⟨fun ht => (hF.incomp [] hnil t ht List.nil_prefix).symm, fun h => h ▸ hnil⟩
end IsFront
end Front
