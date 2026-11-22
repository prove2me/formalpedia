-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:03.262063+00:00
-- url     : https://prove2.me/submissions/797a08e6-f81a-4730-85b9-01be4523433c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Theorems.Thm_BooleanIsoperimetry_macaulay_bc_min
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    H (N + 1) (a + b) ≤ max (H N a) b + max (H N b) a := by
  suffices key : ∀ n, ∀ a b : ℕ, a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a by
    exact key N a b ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hb
    have hS : a + b ≤ 2 ^ (n + 1) := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega
    obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hS
    rw [H_succ_cascade hcasc]
    exact macaulay_bc_min n ih ha hb hp hq hpq hcasc
end BooleanIsoperimetry
