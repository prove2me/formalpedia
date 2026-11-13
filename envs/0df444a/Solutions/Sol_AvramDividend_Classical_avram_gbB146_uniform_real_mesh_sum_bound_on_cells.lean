-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB146_uniform_real_mesh_sum_bound_on_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:14:47.706441+00:00
-- url     : https://prove2.me/submissions/4a503e19-7045-474f-9d45-288be0a2a065

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} (n : ℕ) (hn : 0 < n) (G : ℕ → ℕ → Ω → ℝ)
    (B : ℝ) (hG : ∀ m i ω, |G m i ω| ≤ B) :
    ∀ (m : ℕ) (t : ℝ) (ω : Ω), t ∈ Ico (0 : ℝ) (n : ℝ) →
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      |(Finset.range (m + 1)).sum (fun i =>
        if (i : ℝ) * Δ ≤ t ∧ t < ((i + 1 : ℕ) : ℝ) * Δ
        then G m i ω else 0)| ≤ B := by
  intro m t ω ht Δ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
    (n : ℝ) hnR m (fun i => G m i ω) t ht
  change |(Finset.range (m + 1)).sum (fun i =>
    if (i : ℝ) * Δ ≤ t ∧ t < ((i + 1 : ℕ) : ℝ) * Δ
    then G m i ω else 0)| ≤ B
  rw [show (Finset.range (m + 1)).sum (fun i =>
    if (i : ℝ) * Δ ≤ t ∧ t < ((i + 1 : ℕ) : ℝ) * Δ
    then G m i ω else 0) = G m ⌊t / Δ⌋₊ ω from hs]
  exact hG m ⌊t / Δ⌋₊ ω
