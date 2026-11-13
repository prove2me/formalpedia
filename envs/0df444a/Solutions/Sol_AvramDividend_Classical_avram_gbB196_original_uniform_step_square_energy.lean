-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB196_original_uniform_step_square_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:48:01.099209+00:00
-- url     : https://prove2.me/submissions/fceca8f1-1308-4769-8509-077f4dceb404

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB78_two_grid_step_cross_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_gbB70_uniform_two_grid_weighted_block_regroup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Deterministic one-mesh time energy from the established two-grid identity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (n m : ℕ) (hn : 0 < n) (G : ℕ → ℕ → Ω → ℝ) (hG : ∀ a i, StronglyMeasurable (G a i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ a i ω, |G a i ω| ≤ B) :
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (K m t ω) ^ 2 ∂P) ∂volume) =
      Δ * (Finset.range (m + 1)).sum (fun i =>
        ∫ ω, (G m i ω) ^ 2 ∂P) := by
  let N : ℕ := (m + 1) * (m + 1)
  let E : ℕ → ℝ → Ω → ℝ := fun k t ω =>
    let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
    (Finset.range (k + 1)).sum (fun i =>
      if (s i : ℝ) ≤ t ∧ t < ((s i + δ : ℝ≥0) : ℝ)
      then G k i ω else 0)
  have htime : (∫ t in Ioo (0 : ℝ) (n : ℝ), (∫ ω, (E m t ω)^2 ∂P) ∂volume) =
      ((n : ℝ) / (((m + 1) * (m + 1) : ℕ) : ℝ)) * (Finset.range N).sum (fun r => ∫ ω, (G m (r / (m + 1)) ω)^2 ∂P) := by
    simpa only [E, N, pow_two] using (avram_gbB78_two_grid_step_cross_time_integral P n m m hn G hG hBound)
  let F : ℕ → ℝ := fun r => ∫ ω, (G m (r / (m + 1)) ω)^2 ∂P
  have hdiv (i j : ℕ) (hj : j < m + 1) : (i * (m + 1) + j) / (m + 1) = i := by
    rw [Nat.mul_comm i (m + 1), Nat.mul_add_div (Nat.succ_pos m) i j, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hgroup : (Finset.range N).sum F =
      ((m + 1 : ℕ) : ℝ) * (Finset.range (m + 1)).sum (fun i => ∫ ω, (G m i ω)^2 ∂P) := by
    have h70 := avram_gbB70_uniform_two_grid_weighted_block_regroup m m F (fun _ => (1 : ℝ))
    have h70' : (Finset.range N).sum F =
        (Finset.range (m + 1)).sum (fun i => (Finset.range (m + 1)).sum (fun j => F (i * (m + 1) + j))) := by
      simpa only [N, one_mul] using h70.symm
    calc
      (Finset.range N).sum F = (Finset.range (m + 1)).sum (fun i => (Finset.range (m + 1)).sum (fun j => F (i * (m + 1) + j))) := h70'
      _ = (Finset.range (m + 1)).sum (fun i => ((m + 1 : ℕ) : ℝ) * (∫ ω, (G m i ω)^2 ∂P)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hconst : (Finset.range (m + 1)).sum (fun j => F (i * (m + 1) + j)) =
            (Finset.range (m + 1)).sum (fun _ => ∫ ω, (G m i ω)^2 ∂P) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [F, hdiv i j (Finset.mem_range.mp hj)]
        simpa using hconst
      _ = ((m + 1 : ℕ) : ℝ) * (Finset.range (m + 1)).sum (fun i => ∫ ω, (G m i ω)^2 ∂P) := by
        rw [Finset.mul_sum]
  change (∫ t in Ioo (0 : ℝ) (n : ℝ), (∫ ω, (E m t ω)^2 ∂P) ∂volume) =
      (n : ℝ) / ((m : ℝ) + 1) * (Finset.range (m + 1)).sum (fun i => ∫ ω, (G m i ω)^2 ∂P)
  rw [htime]
  change ((n : ℝ) / (((m + 1) * (m + 1) : ℕ) : ℝ)) * (Finset.range N).sum F =
    (n : ℝ) / ((m : ℝ) + 1) * (Finset.range (m + 1)).sum (fun i => ∫ ω, (G m i ω)^2 ∂P)
  rw [hgroup]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
