-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_embed0_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:32.624498+00:00
-- url     : https://prove2.me/submissions/07b088b6-2ff2-4d1c-a2d5-f0d7bd01fefc

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed1 y) = hDist x y + 1 := by
  unfold hDist
  -- Split the symmetric difference into old coordinates and the new last coordinate.
  have h_symmDiff :
      symmDiff (embed0 x) (embed1 y) =
        Finset.image Fin.castSucc (symmDiff x y) ∪ {Fin.last n} := by
    ext i
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp [embed0, embed1, Finset.mem_symmDiff, Finset.mem_image,
        (Fin.castSucc_injective n).eq_iff, (Fin.castSucc_lt_last j).ne]
    · simp [embed0, embed1, Finset.mem_symmDiff, Finset.mem_image,
        fun a : Fin n => (Fin.castSucc_lt_last a).ne]
  rw [h_symmDiff, Finset.card_union_of_disjoint] <;>
    norm_num [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
end BooleanIsoperimetry
