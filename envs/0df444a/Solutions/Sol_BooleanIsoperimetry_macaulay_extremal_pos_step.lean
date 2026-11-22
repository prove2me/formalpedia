-- Prove2me | solution 1 for BooleanIsoperimetry.macaulay_extremal_pos_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:40.050897+00:00
-- url     : https://prove2.me/submissions/6614899d-b2da-4421-a02a-9ad5f21a5111

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
public import Theorems.Thm_BooleanIsoperimetry_macaulay_extremal_pos_step_LE
public import Theorems.Thm_BooleanIsoperimetry_macaulay_extremal_pos_step_GT
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_comm
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_gt
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_le
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  cases le_total b a with
  | inl hba =>
      rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : a ≤ H n b
      · rw [boundaryCost_eq_case_le ha hba hcase]
        exact macaulay_extremal_pos_step_LE n ih ha hb hp hq hpq hcasc hq_pos hba hcase
      · push Not at hcase
        rw [boundaryCost_eq_case_gt ha hba hcase]
        exact macaulay_extremal_pos_step_GT n ih ha hb hp hq hpq hcasc hq_pos hba hcase
  | inr hab =>
      rw [boundaryCost_comm n a b]
      have hpq_symm : p + q = b + a := by omega
      have hcasc_symm : CascadeSplit n (b + a) p q := by
        simpa [Nat.add_comm] using hcasc
      rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : b ≤ H n a
      · rw [boundaryCost_eq_case_le hb hab hcase]
        exact macaulay_extremal_pos_step_LE n ih hb ha hp hq hpq_symm hcasc_symm hq_pos hab hcase
      · push Not at hcase
        rw [boundaryCost_eq_case_gt hb hab hcase]
        exact macaulay_extremal_pos_step_GT n ih hb ha hp hq hpq_symm hcasc_symm hq_pos hab hcase
end BooleanIsoperimetry
