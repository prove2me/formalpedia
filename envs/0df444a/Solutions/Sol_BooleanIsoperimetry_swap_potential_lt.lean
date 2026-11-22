-- Prove2me | solution 1 for BooleanIsoperimetry.swap_potential_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:28.653853+00:00
-- url     : https://prove2.me/submissions/185fdc4a-c6b8-43e2-b60c-362c3fb9c813

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {x y : Cube N}
    (hx : x ∈ A) (hy : y ∉ A) (hlt : simplicialLt y x)
    (heq : A' = insert y (A.erase x)) :
    compressionPotential A' < compressionPotential A := by
  have hrank : rank y < rank x := rank_strictMono hlt
  have hynm : y ∉ A.erase x := by simp [Finset.mem_erase, hy]
  have hsum_insert : compressionPotential A' = rank y + ∑ z ∈ A.erase x, rank z := by
    rw [heq]; unfold compressionPotential; rw [Finset.sum_insert hynm]
  have hsum_erase : (∑ z ∈ A.erase x, rank z) + rank x = compressionPotential A := by
    unfold compressionPotential; rw [Finset.sum_erase_add A _ hx]
  omega
end BooleanIsoperimetry
