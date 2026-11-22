-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_splitPrefixMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:11.357298+00:00
-- url     : https://prove2.me/submissions/ae981990-5835-46a9-b15d-7c58c05b4e06

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pascal
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pred_add_choosePred
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_choose_succ_dim
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) (l : ℕ) :
    splitPrefixMass n p q l =
      min k (binomPrefix n (l + 1) + binomPrefix n l) := by
  rcases h with ⟨r, t, hCascade, hp, hq⟩
  have hBr : binomPrefix n (r - 1) + choosePred n r = binomPrefix n r :=
    binomPrefix_pred_add_choosePred n r
  have hCr1 : binomPrefix n (r + 1) = binomPrefix n r + Nat.choose n r := by
    exact binomPrefix_succ n r
  generalize_proofs at *
  obtain ⟨hr, ht, hk, h⟩ := hCascade
  generalize_proofs at *
  have htC : t ≤ Nat.choose n r + choosePred n r := by
    exact ht.trans (by rw [choose_succ_dim])
  generalize_proofs at *
  rcases lt_trichotomy l r with (hl | rfl | hr) <;>
    simp_all +decide only [splitPrefixMass, cascadeSlice0Value, cascadeSlice1Value]
  · unfold cappedPrefixMass
    simp +decide only [binomPrefix_pascal]
    rw [min_eq_right, min_eq_right, min_eq_right]
    · exact le_add_of_le_of_nonneg
        (add_le_add (binomPrefix_mono _ (by omega)) (binomPrefix_mono _ (by omega)))
        (Nat.zero_le _)
    · exact le_add_of_le_of_nonneg (binomPrefix_mono _ (Nat.le_sub_one_of_lt hl))
        (Nat.zero_le _)
    · exact le_add_right (binomPrefix_mono _ (by linarith))
  · rcases l with (_ | l)
    · unfold cappedPrefixMass
      simp only [binomPrefix_pascal]
      omega
    · unfold cappedPrefixMass
      simp only [binomPrefix_pascal]
      omega
  · have h_binomPrefix_ge :
        binomPrefix n (l + 1) ≥ binomPrefix n (r + 1) ∧
          binomPrefix n l ≥ binomPrefix n r := by
      exact ⟨binomPrefix_mono _ (by linarith), binomPrefix_mono _ (by linarith)⟩
    generalize_proofs at *
    unfold cappedPrefixMass
    simp_all +decide only [binomPrefix_pascal, ge_iff_le]
    grind
end BooleanIsoperimetry
