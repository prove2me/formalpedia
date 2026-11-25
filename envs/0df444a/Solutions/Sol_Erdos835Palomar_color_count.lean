-- Prove2me | solution 1 for Erdos835Palomar.color_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:22:13.683805+00:00
-- url     : https://prove2.me/submissions/2c59cc16-feb9-4f2d-bcc8-6c53cbd364d4

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_card_supersets
public import Theorems.Thm_Erdos835Palomar_card_color_in

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (i : Fin (k + 1)) (j : ℕ) (hj : 1 ≤ j) (W : Finset (Fin (2 * k))) (hW : #W = k + j) :
    (k + 1) * #({s | s.val ⊆ W ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) =
      (k + j).choose j := by
  set S : Finset {s : Finset (Fin (2 * k)) // #s = k} := {s | s.val ⊆ W ∧ c s = i} with hSdef
  have hdc := card_mul_eq_card_mul
      (fun (s : {s : Finset (Fin (2 * k)) // #s = k}) (A : Finset (Fin (2 * k))) => s.val ⊂ A)
      (s := S) (t := powersetCard (k + 1) W) (m := j) (n := 1)
    (by
      intro s hs
      simp only [hSdef, mem_filter, mem_univ, true_and] at hs
      have := card_supersets W s.val hs.1
      rw [s.2, hW] at this
      simp only [bipartiteAbove]
      rw [this]; omega)
    (by
      intro A hA
      rw [mem_powersetCard] at hA
      have h1 := card_color_in c hc A hA.2 i
      simp only [bipartiteBelow]
      rw [← h1]
      congr 1
      ext s
      simp only [hSdef, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hci⟩, hsA⟩; exact ⟨hsA, hci⟩
      · rintro ⟨hsA, hci⟩; exact ⟨⟨hsA.subset.trans hA.1, hci⟩, hsA⟩)
  rw [card_powersetCard, hW, mul_one] at hdc
  have hid : (k + j).choose (k + 1) * (k + 1) = (k + j).choose j * j := by
    rw [Nat.choose_succ_right_eq, Nat.choose_symm_add]
    congr 1; omega
  have : (k + 1) * #S * j = (k + j).choose j * j := by
    rw [← hid, ← hdc]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) this
end Erdos835Palomar
