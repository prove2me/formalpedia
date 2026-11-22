-- Prove2me | solution 1 for BooleanIsoperimetry.downMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:50.027795+00:00
-- url     : https://prove2.me/submissions/6c4a5232-ee24-4c62-89a2-84bbba990839

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    Set.InjOn (downMap i A) ↑A := by
  intro x hx y hy h
  rw [Finset.mem_coe] at hx hy
  unfold downMap at h
  by_cases hcx : i ∈ x ∧ x.erase i ∉ A
  · by_cases hcy : i ∈ y ∧ y.erase i ∉ A
    · rw [if_pos hcx, if_pos hcy] at h
      have := congrArg (insert i) h
      rwa [Finset.insert_erase hcx.1, Finset.insert_erase hcy.1] at this
    · rw [if_pos hcx, if_neg hcy] at h
      rw [← h] at hy; exact (hcx.2 hy).elim
  · by_cases hcy : i ∈ y ∧ y.erase i ∉ A
    · rw [if_neg hcx, if_pos hcy] at h
      rw [h] at hx; exact (hcy.2 hx).elim
    · rw [if_neg hcx, if_neg hcy] at h
      exact h
end BooleanIsoperimetry
