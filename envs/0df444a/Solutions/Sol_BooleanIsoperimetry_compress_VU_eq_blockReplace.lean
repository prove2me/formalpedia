-- Prove2me | solution 1 for BooleanIsoperimetry.compress_VU_eq_blockReplace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:02.170804+00:00
-- url     : https://prove2.me/submissions/5ba5cde7-6a0b-4cd6-9bf6-c8fa04b66ef0

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (S : Cube N) :
    UV.compress V U S = (if U ⊆ S ∧ Disjoint V S then blockReplace U V S else S) := by
  unfold UV.compress blockReplace
  by_cases h : U ⊆ S ∧ Disjoint V S
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, Finset.sup_eq_union, Finset.union_sdiff_distrib]
    have hVU : V \ U = V := (Finset.sdiff_eq_self_iff_disjoint).2 hd.symm
    rw [hVU]
  · rw [if_neg h, if_neg (by tauto)]
end BooleanIsoperimetry
