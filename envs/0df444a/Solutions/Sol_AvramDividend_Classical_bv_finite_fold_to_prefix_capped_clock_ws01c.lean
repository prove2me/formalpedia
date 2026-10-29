-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_fold_to_prefix_capped_clock_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:55:26.281257+00:00
-- url     : https://prove2.me/submissions/0709728b-3005-4901-aa7b-e1db04b1b6db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_foldr_min_eq_finite_iInf_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_fold_horizon_vs_top_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal Classical

theorem solution
    (M : ℕ) (x : ℕ → ℝ≥0∞) (hit : ℕ → Prop)
    (H T : ℝ≥0∞) (hTH : T ≤ H) :
    (((List.range (M + 1)).foldr
        (fun k u => (if hit k then x k else H) ⊓ u) H) ⊓ T) =
      ((⨅ (k : ℕ) (_ : k ≤ M),
          if hit k then x k else ⊤) ⊓ T) := by
  let L : List ℕ := List.range (M + 1)
  let fH : ℕ → ℝ≥0∞ := fun k => if hit k then x k else H
  let fTop : ℕ → ℝ≥0∞ := fun k => if hit k then x k else ⊤
  change (L.foldr (fun k u => fH k ⊓ u) H) ⊓ T =
    (⨅ (k : ℕ) (_ : k ≤ M), fTop k) ⊓ T
  calc
    (L.foldr (fun k u => fH k ⊓ u) H) ⊓ T =
        (⨅ (k : ℕ) (_ : k ∈ L), fH k) ⊓ T := by
          rw [bv_foldr_min_eq_finite_iInf_ws01c]
          rw [inf_assoc, inf_eq_right.mpr hTH]
    _ = L.foldr (fun k u => fH k ⊓ u) T := by
          rw [bv_foldr_min_eq_finite_iInf_ws01c]
    _ = L.foldr (fun k u => fTop k ⊓ u) T := by
          exact bv_finite_fold_horizon_vs_top_ws01c L x hit H T hTH
    _ = (⨅ (k : ℕ) (_ : k ∈ L), fTop k) ⊓ T :=
          bv_foldr_min_eq_finite_iInf_ws01c fTop L T
    _ = (⨅ (k : ℕ) (_ : k ≤ M), fTop k) ⊓ T := by
          simp only [L, List.mem_range, Nat.lt_succ_iff]
