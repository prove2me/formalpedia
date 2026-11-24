-- Prove2me | solution 1 for BondySimonovits.ecount_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:57.729173+00:00
-- url     : https://prove2.me/submissions/db7d8a5f-7e47-47d5-9d8f-28f64e744117

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] (X : Finset V) (u : V)
    (hu : u ∈ X) :
    ecount K X X = ecount K (X.erase u) (X.erase u) + 2 * (X.filter (K.Adj u)).card := by
  set X' := X.erase u with hX'
  have hX : X = insert u X' := (Finset.insert_erase hu).symm
  have huX' : u ∉ X' := Finset.notMem_erase u X
  have h1 : ∀ a, (X.filter (K.Adj a)).card =
      (X'.filter (K.Adj a)).card + if K.Adj a u then 1 else 0 := by
    intro a
    rw [hX, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [huX'])]
    · rfl
  have h2 : (X.filter (K.Adj u)).card = (X'.filter (K.Adj u)).card := by
    rw [h1]; simp
  have h3 : ∑ a ∈ X', (if K.Adj a u then 1 else 0) = (X'.filter (K.Adj u)).card := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun a _ => by simp [K.adj_comm])
  clear_value X'
  unfold ecount
  calc ∑ a ∈ X, (X.filter (K.Adj a)).card
      = (X.filter (K.Adj u)).card + ∑ a ∈ X', (X.filter (K.Adj a)).card := by
        rw [hX, Finset.sum_insert huX']
    _ = (X.filter (K.Adj u)).card + ∑ a ∈ X', ((X'.filter (K.Adj a)).card +
          if K.Adj a u then 1 else 0) := by
        rw [Finset.sum_congr rfl (fun a _ => h1 a)]
    _ = _ := by rw [Finset.sum_add_distrib, h3, ← h2]; ring
end BondySimonovits
