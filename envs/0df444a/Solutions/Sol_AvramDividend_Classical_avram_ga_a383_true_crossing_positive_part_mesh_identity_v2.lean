-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:02:52.352417+00:00
-- url     : https://prove2.me/submissions/7d140c98-f273-4919-b382-0cab7bf38416

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a380_monotone_grid_unique_crossing_v2
import Theorems.Thm_AvramDividend_Classical_avram_ga_a381_unique_masked_sum_pospart_v2
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (m : ℕ) (Δ ρ : ℝ≥0) (hΔ : 0 < Δ) (f : ℕ → ℝ) :
    max (∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ < ρ ∧ ρ < (i : ℝ≥0) * Δ + Δ
      then f i else 0) 0 =
    ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ < ρ ∧ ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) * Δ
      then max (if ρ < ((Nat.succ i : ℕ) : ℝ≥0) * Δ then f i else 0) 0
      else 0 := by
  classical
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Mask : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
  have hStep (i : ℕ) : s i + Δ = s (i + 1) := by
    dsimp [s]
    rw [Nat.cast_succ, add_mul, one_mul]
  have hStrict : StrictMono s := by
    intro i k hik
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hik) hΔ
  have hUnique : ∀ i k, Mask i → Mask k → i = k := by
    intro i k hi hk
    apply avram_ga_a380_monotone_grid_unique_crossing_v2 s hStrict ρ i k
    · exact ⟨hi.1, by simpa only [hStep] using hi.2⟩
    · exact ⟨hk.1, by simpa only [hStep] using hk.2⟩
  have hSum := avram_ga_a381_unique_masked_sum_pospart_v2 m Mask f hUnique
  change max (∑ i ∈ Finset.range m,
    if Mask i then f i else 0) 0 = _
  rw [hSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hclock : (((Nat.succ i : ℕ) : ℝ≥0) * Δ) = s i + Δ :=
    (hStep i).symm
  rw [hclock]
  by_cases hs : s i < ρ
  · have hs' : (i : ℝ≥0) * Δ < ρ := hs
    by_cases ht : ρ < s i + Δ
    · simp [Mask, hs, hs', ht, le_of_lt ht]
    · simp [Mask, hs, hs', ht]
  · have hs' : ¬ (i : ℝ≥0) * Δ < ρ := hs
    simp [Mask, hs, hs']
