-- Prove2me | solution 1 for Erdos266.bad_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:49.205805+00:00
-- url     : https://prove2.me/submissions/0ae6cfe8-47da-4d12-9dc9-857bda8b52f3

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}
namespace Erdos266
theorem _root_.solution (ha : StrictMono a) (i : ℕ) :
    {n : ℕ | ∃ j ∈ range i, (a n : ℚ) + tSeq j = 0}.Finite := by
  have hsub : {n : ℕ | ∃ j ∈ range i, (a n : ℚ) + tSeq j = 0}
      ⊆ ⋃ j ∈ (↑(range i) : Set ℕ), {n : ℕ | (a n : ℚ) + tSeq j = 0} := by
    intro n hn
    obtain ⟨j, hj, hjn⟩ := hn
    exact Set.mem_biUnion (Finset.mem_coe.mpr hj) hjn
  refine Set.Finite.subset (Set.Finite.biUnion (range i).finite_toSet
    fun j _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  simp only [Set.mem_ofPred_eq] at hx hy
  have hxy : (a x : ℚ) = (a y : ℚ) := by linarith
  exact ha.injective (by exact_mod_cast hxy)
end Erdos266
