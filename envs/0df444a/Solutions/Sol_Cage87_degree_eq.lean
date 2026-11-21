-- Prove2me | solution 1 for Cage87.degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:36.531159+00:00
-- url     : https://prove2.me/submissions/0d38c650-15d6-4718-aab1-3aabd173f252

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_nb_length
public import Theorems.Thm_Cage87_nb_nodup
public import Theorems.Thm_Cage87_G_adj
attribute [local simp] Cage87.G_adj

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution (v : Fin 768) : G.degree v = 8 := by
  rw [← card_neighborFinset_eq_degree]
  have h : (G.neighborFinset v).map ⟨Fin.val, Fin.val_injective⟩ = (nb adj v.val).toFinset := by
    ext z
    simp only [Finset.mem_map, mem_neighborFinset, G_adj, Function.Embedding.coeFn_mk,
      List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨⟨z, (nb_prop v.2 hz).1⟩, hz, rfl⟩
  rw [← Finset.card_map, h, List.toFinset_card_of_nodup (nb_nodup v.2), nb_length v.2]
end Cage87
