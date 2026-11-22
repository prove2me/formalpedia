-- Prove2me | solution 1 for BooleanIsoperimetry.H_inequality_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:05:36.906075+00:00
-- url     : https://prove2.me/submissions/5a29e35b-e1fa-43c6-8874-2a7fec24626d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_interleaving_boundaryCost_mono
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_canonicalSplit_interleaves
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  intro n a b ha hb
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, _, _, _, h_casc⟩ := exists_cascade_split n (a + b) hab
  have h_inter := canonicalSplit_interleaves ha hb h_casc
  have h_mono := interleaving_boundaryCost_mono ha hb h_inter
  have h_succ := H_succ_cascade h_casc
  unfold boundaryCost at h_mono
  rw [h_succ]
  exact h_mono
end BooleanIsoperimetry
