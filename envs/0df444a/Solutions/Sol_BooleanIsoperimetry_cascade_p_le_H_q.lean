-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_p_le_H_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:54.944585+00:00
-- url     : https://prove2.me/submissions/f2283c8d-7837-498e-a9eb-3bd7fef27882

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade
public import Theorems.Thm_BooleanIsoperimetry_simplicialLt_embed1_embed0
public import Theorems.Thm_BooleanIsoperimetry_empty_mem_initSeg
public import Theorems.Thm_BooleanIsoperimetry_card_gShift
public import Theorems.Thm_BooleanIsoperimetry_hDist_gShift_le
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono
public import Theorems.Thm_BooleanIsoperimetry_slice1_initSeg_eq
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) (hq : 1 ≤ q) :
    p ≤ H n q := by
  -- By `slice_card_eq_cascade h`, we know that `slice0 (simplicialInitSeg (n + 1) k).card = p`
  -- and `slice1 (simplicialInitSeg (n + 1) k).card = q`.
  obtain ⟨h_slice0, h_slice1⟩ := slice_card_eq_cascade h
  -- We need to show that
  -- `slice0 (simplicialInitSeg (n + 1) k) ⊆ neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k))`.
  have h_subset : slice0 (simplicialInitSeg (n + 1) k) ⊆
      neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k)) := by
    intro x hx; by_cases hx' : x = ∅ <;> simp_all +decide only [mem_neighborhood_iff]
    · exact ⟨_, empty_mem_initSeg (by linarith) |> fun h => slice1_initSeg_eq ▸ h,
        by simp +decide [hDist]⟩
    · refine ⟨ gShift x, ?_, ?_ ⟩ <;>
        simp_all +decide only [slice0, slice1, Finset.mem_filter, Finset.mem_univ, true_and]
      · -- Since $x \neq \emptyset$, we have
        -- $gShift x \in \text{slice1} (\text{simplicialInitSeg} (n + 1) k)$.
        have h_gShift_mem : simplicialLt (embed1 (gShift x)) (embed0 x) := by
          rw [simplicialLt_embed1_embed0]
          rw [card_gShift]
          exact Nat.succ_le_of_lt
            (Nat.sub_lt (Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hx')) zero_lt_one)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_lt_of_le (rank_strictMono h_gShift_mem) (Finset.mem_filter.mp hx |>.2.le)⟩
      · exact hDist_gShift_le x
  have h_card_subset : (neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k))).card ≤ H n q := by
    rw [slice1_initSeg_eq, h_slice1]
    rfl
  exact h_slice0 ▸ le_trans (Finset.card_le_card h_subset) h_card_subset
end BooleanIsoperimetry
