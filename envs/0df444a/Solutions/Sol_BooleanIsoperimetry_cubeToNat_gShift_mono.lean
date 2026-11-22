-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_gShift_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:47.128357+00:00
-- url     : https://prove2.me/submissions/42285cb6-9135-4fe4-bc61-c1c5083272d7

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_erase
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_lt_two_pow
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_gShift_le
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_gShift_erase_max
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} :
    ∀ (m : ℕ) (s t : Cube n), s.card = m → t.card = m → cubeToNat t ≤ cubeToNat s →
      cubeToNat (gShift t) ≤ cubeToNat (gShift s) := by
  -- We proceed by induction on $m$.
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
  intro s t hs ht h
  by_cases hm : m ≤ 1
  · interval_cases m <;>
      simp_all +decide only [not_lt_zero, not_isEmpty_of_nonempty, IsEmpty.forall_iff,
        implies_true, Finset.card_eq_zero, le_refl, Nat.lt_one_iff, Finset.card_eq_one]
    unfold gShift; aesop
  · -- Let Ms = s.max' (nonempty) and Mt = t.max'.
    obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms ∈ s ∧ ∀ i ∈ s, i ≤ Ms := by
      exact ⟨ Finset.max' s (Finset.card_pos.mp (by linarith) ), Finset.max'_mem _ _,
        fun i hi => Finset.le_max' _ _ hi ⟩
    obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt ∈ t ∧ ∀ i ∈ t, i ≤ Mt := by
      exact ⟨ Finset.max' t (Finset.card_pos.mp (by linarith) ), Finset.max'_mem _ _,
        fun i hi => Finset.le_max' _ _ hi ⟩
    by_cases hMtMs : Mt < Ms
    · -- The peeled form of `gShift s` contains the top term `2 ^ (Ms : ℕ)`.
      have h_cubeToNat_gShift_s : cubeToNat (gShift s) ≥ 2 ^ (Ms : ℕ) := by
        rw [cubeToNat_gShift_erase_max]
        any_goals exact Finset.card_pos.mp (by linarith)
        · exact le_add_of_nonneg_of_le (Nat.zero_le _) (by
            rw [show Finset.max' s (Finset.card_pos.mp (by linarith) ) = Ms from
              le_antisymm (hMs.2 _ (Finset.max'_mem _ _) )
                (Finset.le_max' _ _ hMs.1)])
        · linarith
      -- By cubeToNat_lt_two_pow, cubeToNat t < 2^(Ms:ℕ).
      have h_cubeToNat_t : cubeToNat t < 2 ^ (Ms : ℕ) := by
        apply cubeToNat_lt_two_pow
        exact fun i hi => lt_of_le_of_lt (hMt.2 i hi) hMtMs
      exact le_trans (cubeToNat_gShift_le _) (by linarith)
    · by_cases hMsMt : Ms < Mt
      · have h_contra : cubeToNat s < 2 ^ (Mt : ℕ) := by
          apply cubeToNat_lt_two_pow
          exact fun i hi => lt_of_le_of_lt (hMs.2 i hi) hMsMt
        have h_contra : 2 ^ (Mt : ℕ) ≤ cubeToNat t := by
          have h_contra : cubeToNat t = cubeToNat (t.erase Mt) + 2 ^ (Mt : ℕ) := by
            exact cubeToNat_erase hMt.1
          exact h_contra.symm ▸ Nat.le_add_left _ _
        linarith
      · -- With `¬ Ms < Mt` and `¬ Mt < Ms` the two maxima coincide.
        obtain rfl : Ms = Mt := le_antisymm (not_lt.mp hMtMs) (not_lt.mp hMsMt)
        rw [not_le] at hm
        -- Apply the induction hypothesis after erasing the common maximum.
        have h_ind : cubeToNat (gShift (t.erase Ms)) ≤ cubeToNat (gShift (s.erase Ms)) := by
          apply ih (m - 1) (by
          exact Nat.pred_lt (ne_bot_of_gt hm)) (s.erase Ms) (t.erase Ms)
          · rw [Finset.card_erase_of_mem hMs.1, hs]
          · rw [Finset.card_erase_of_mem hMt.1, ht]
          · have h_erase :
                cubeToNat t = cubeToNat (t.erase Ms) + 2 ^ (Ms : ℕ) ∧
                  cubeToNat s = cubeToNat (s.erase Ms) + 2 ^ (Ms : ℕ) := by
              exact ⟨ cubeToNat_erase hMt.1, cubeToNat_erase hMs.1 ⟩
            linarith
        convert add_le_add_right h_ind (2 ^ (Ms : ℕ) ) using 1
        · rw [add_comm, cubeToNat_gShift_erase_max]
          focus
            rw [show Finset.max' t _ = Ms from
              le_antisymm (hMt.2 _ (Finset.max'_mem _ _) ) (Finset.le_max' _ _ hMt.1)]
          · exact ⟨ Ms, hMt.1 ⟩
          · grind
        · rw [add_comm, cubeToNat_gShift_erase_max]
          focus
            rw [show Finset.max' s _ = Ms from
              le_antisymm (hMs.2 _ (Finset.max'_mem _ _) ) (Finset.le_max' _ _ hMs.1)]
          · exact ⟨ Ms, hMs.1 ⟩
          · linarith
end BooleanIsoperimetry
