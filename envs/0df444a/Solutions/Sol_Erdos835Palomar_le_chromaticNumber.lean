-- Prove2me | solution 1 for Erdos835Palomar.le_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:17:11.44075+00:00
-- url     : https://prove2.me/submissions/5209828c-e56a-458c-8acb-7b45b3396d23

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_card_ssubsets
public import Theorems.Thm_Erdos835Palomar_adj_of_ssubset

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (hk : 0 < k) : (k + 1 : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
  obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k + 1)
    (by rw [card_univ, Fintype.card_fin]; omega)
  have hcl : J(2 * k, k).IsClique
      (({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}) : Set _) := by
    intro s hs t ht hst
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
    exact adj_of_ssubset hA hs ht hst
  have := hcl.card_le_chromaticNumber
  rw [card_ssubsets hA] at this
  exact_mod_cast this
end Erdos835Palomar
