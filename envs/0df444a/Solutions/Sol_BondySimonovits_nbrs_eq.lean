-- Prove2me | solution 1 for BondySimonovits.nbrs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:02.126006+00:00
-- url     : https://prove2.me/submissions/762d36a3-c8a1-456d-bd10-1094eaea5979

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_mem_layer
public import Theorems.Thm_BondySimonovits_adj_levels


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
namespace BondySimonovits
theorem _root_.solution (x : V) (i : ℕ) (u : V) (hu : u ∈ layer K x i) :
    univ.filter (K.Adj u) = (layer K x (i - 1) ∪ layer K x (i + 1)).filter (K.Adj u) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, mem_layer]
  constructor
  · intro h
    rw [mem_layer] at hu
    obtain ⟨hv, hd⟩ := adj_levels K f hf hu.1 h
    refine ⟨?_, h⟩
    rcases hd with hd | hd
    · exact Or.inr ⟨hv, by omega⟩
    · exact Or.inl ⟨hv, by omega⟩
  · exact fun h => h.2
end BondySimonovits
