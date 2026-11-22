-- Prove2me | solution 1 for BooleanIsoperimetry.gShift_le_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:06.683487+00:00
-- url     : https://prove2.me/submissions/86d6a451-63a2-4613-a062-fdf4c7fef355

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
theorem _root_.solution {n : ℕ} {u v : Cube n} (h : hDist u v ≤ 1) :
    simplicialLe (gShift v) u := by
  obtain h | h := h.eq_or_lt
  · simp_all +decide only [le_refl]
    -- Distance one means one side erases a single coordinate from the other.
    obtain ⟨c, hc⟩ : ∃ c, (u = v.erase c ∧ c ∈ v) ∨ (v = u.erase c ∧ c ∈ u) := by
      obtain ⟨ c, hc ⟩ := Finset.card_eq_one.mp h
      use c
      simp_all +decide [Finset.ext_iff, symmDiff]
      grind
    obtain hc | hc := hc
    · simp_all +decide only [simplicialLe, Finset.card_erase_of_mem]
      -- Since c ∈ v, gShift v = v.erase (v.min' ·).
      have h_gShift_v : gShift v = v.erase (v.min' (by
      exact ⟨ c, hc.2 ⟩)) := by
        unfold gShift; aesop
      generalize_proofs at *
      by_cases h_cases : c = v.min' ‹_›
      · simp_all +decide only [Finset.card_erase_of_mem, lt_self_iff_false, le_refl,
          and_self, or_true]
      · simp_all +decide only
        refine Or.inr ⟨ ?_, ?_ ⟩
        · exact Finset.card_erase_of_mem (Finset.min'_mem _ ‹_›)
        · unfold cubeToNat
          rw [← Finset.sum_erase_add _ _
              (Finset.mem_erase_of_ne_of_mem (Ne.symm h_cases) (Finset.min'_mem _ ‹_›) ),
            ← Finset.sum_erase_add _ _ (Finset.mem_erase_of_ne_of_mem h_cases hc.2)]
          rw [Finset.erase_right_comm]
          exact Nat.add_le_add_left
            (pow_le_pow_right₀ (by decide) (Finset.min'_le _ _ hc.2) ) _
    · simp_all +decide only [simplicialLe]
      unfold gShift
      grind +suggestions
  · simp_all +decide only [Nat.lt_one_iff, zero_le]
    simp_all +decide only [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty]
    unfold gShift
    by_cases hv : v.Nonempty
    · simp_all +decide only [simplicialLe, ↓reduceDIte]
      exact Or.inl (Finset.card_lt_card (Finset.erase_ssubset (Finset.min'_mem _ hv) ))
    · simp_all +decide only [Finset.not_nonempty_iff_eq_empty, simplicialLe,
        Finset.not_nonempty_empty,
        ↓reduceDIte, Finset.card_empty, lt_self_iff_false, le_refl, and_self, or_true]
end BooleanIsoperimetry
