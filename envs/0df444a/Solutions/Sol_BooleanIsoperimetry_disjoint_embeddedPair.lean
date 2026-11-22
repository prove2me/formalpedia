-- Prove2me | solution 1 for BooleanIsoperimetry.disjoint_embeddedPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:24.218159+00:00
-- url     : https://prove2.me/submissions/f19ceddd-c485-44a8-b789-b0e8484e83eb

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
public import Theorems.Thm_BooleanIsoperimetry_compression_last_not_mem_embed0
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    Disjoint (A.image embed0) (B.image embed1) := by
  rw [Finset.disjoint_left]
  intro x hx0 hx1
  rcases Finset.mem_image.mp hx0 with ⟨a, _ha, rfl⟩
  rcases Finset.mem_image.mp hx1 with ⟨b, _hb, hb⟩
  have hlast : Fin.last N ∈ embed1 b := by simp [embed1]
  rw [hb] at hlast
  exact compression_last_not_mem_embed0 a hlast
end BooleanIsoperimetry
