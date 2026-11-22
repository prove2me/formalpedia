-- Prove2me | solution 1 for BooleanIsoperimetry.card_filter_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:23.485893+00:00
-- url     : https://prove2.me/submissions/7e402dd5-afa7-49e2-bc78-7a0c3d4f392d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card = c)).card = Nat.choose n c := by
  rw [show (Finset.univ.filter (fun w : Cube n => w.card = c))
        = Finset.powersetCard c (Finset.univ : Finset (Fin n)) by
      ext w; simp [Finset.mem_powersetCard]]
  rw [Finset.card_powersetCard]; simp
end BooleanIsoperimetry
