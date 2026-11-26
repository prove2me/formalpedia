-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_diff_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:34.42167+00:00
-- url     : https://prove2.me/submissions/8fceab81-c445-4a33-8ea8-b052ecf99671

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_dIn_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
open Classical
namespace ErdosRubinTaylor
theorem _root_.solution (G : SimpleGraph V) {T : Set V} {u : V} (hu : u ∈ T) (x : V) :
    dIn G T x = dIn G (T \ {u}) x + if G.Adj x u then 1 else 0 := by
  classical
  rw [dIn_eq, dIn_eq]
  by_cases hadj : G.Adj x u
  · have : univ.filter (fun w => w ∈ T ∧ G.Adj x w) =
        insert u (univ.filter (fun w => w ∈ T \ {u} ∧ G.Adj x w)) := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_insert, Set.mem_sdiff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hwu : w = u
        · exact Or.inl hwu
        · exact Or.inr ⟨⟨h1, hwu⟩, h2⟩
      · rintro (rfl | ⟨⟨h1, _⟩, h2⟩)
        · exact ⟨hu, hadj⟩
        · exact ⟨h1, h2⟩
    rw [this, card_insert_of_notMem (by simp)]; simp [hadj]
  · simp only [hadj, ite_false, add_zero]
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun h => hadj (h ▸ h2)⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
end ErdosRubinTaylor
