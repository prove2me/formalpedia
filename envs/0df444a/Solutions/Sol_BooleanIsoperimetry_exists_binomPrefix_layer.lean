-- Prove2me | solution 1 for BooleanIsoperimetry.exists_binomPrefix_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:03.456264+00:00
-- url     : https://prove2.me/submissions/94515e7d-8792-4936-ba77-005843f011c9

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
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_full
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N b : ℕ) (hb : b < 2 ^ N) :
    ∃ r, r ≤ N ∧ binomPrefix N r ≤ b ∧ b < binomPrefix N (r + 1) := by
  -- Let's choose the largest $r$ such that $binomPrefix N r \leq b$.
  obtain ⟨r, hr⟩ : ∃ r ≤ N, binomPrefix N r ≤ b ∧ ∀ s > r, s ≤ N → binomPrefix N s > b := by
    obtain ⟨r0, hr0N, hr0b⟩ : ∃ r ≤ N, binomPrefix N r ≤ b :=
      ⟨0, Nat.zero_le _, by simp +decide [binomPrefix_zero]⟩
    have hne : (Finset.filter (fun r => binomPrefix N r ≤ b) (Finset.Iic N)).Nonempty :=
      ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hr0N, hr0b⟩⟩
    have hmem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    exact ⟨Finset.max' _ hne, Finset.mem_Iic.mp hmem.1, hmem.2,
      fun s hs₁ hs₂ => not_le.mp fun hs₃ => hs₁.not_ge <| Finset.le_max' _ _ <| by aesop⟩
  rcases hr with ⟨hrN, hrle, hmax⟩
  refine ⟨r, hrN, hrle, ?_⟩
  by_cases hlt : r < N
  · exact hmax (r + 1) (by omega) (by omega)
  · have hr_eq : r = N := by omega
    subst r
    rw [binomPrefix_full]
    exact hb
end BooleanIsoperimetry
