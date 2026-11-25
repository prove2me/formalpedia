-- Prove2me | solution 1 for Erdos835Palomar.property_of_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:17:14.288162+00:00
-- url     : https://prove2.me/submissions/52c0546f-513e-4ce0-be5c-94723235c243

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
theorem _root_.solution (C : J(2 * k, k).Coloring (Fin (k + 1))) : Property k := by
  refine ⟨C, fun A hA => eq_univ_of_card _ ?_⟩
  rw [card_image_of_injOn, card_ssubsets hA, Fintype.card_fin]
  intro s hs t ht hst
  by_contra hne
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  exact C.valid (adj_of_ssubset hA hs ht hne) hst
end Erdos835Palomar
