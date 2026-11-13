-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_event_uniform_mesh_positive_pair_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:28:57.802811+00:00
-- url     : https://prove2.me/submissions/4ddf3a00-06f1-4997-bc10-e032c13222d0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (F : Finset ℝ≥0) (T : ℝ≥0) :
    ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ u ∈ F, ∀ v ∈ F, u < v →
          (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by
  obtain ⟨δ, hδ, hgap⟩ :=
    avram_wave7_06_finite_NNReal_marked_times_pairwise_gap F
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨k₀ + 1, Nat.succ_pos k₀, ?_⟩
  intro k hk u hu v hv huv
  have hle := hgap u hu v hv (ne_of_lt huv)
  have huv' : (u : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast (le_of_lt huv)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv')] at hle
  have hkn : ((k₀ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hTreal : (T : ℝ) < ((k₀ + 1 : ℕ) : ℝ) * δ := by
    apply (div_lt_iff₀ hδ).mp
    exact lt_of_lt_of_le hk₀ (by exact_mod_cast Nat.le_succ k₀)
  exact lt_of_lt_of_le hTreal
    (le_trans (mul_le_mul_of_nonneg_left hle (by positivity))
      (mul_le_mul_of_nonneg_right hkn (sub_nonneg.mpr huv')))
