-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB90_finite_time_step_sum_linearity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:38:32.746201+00:00
-- url     : https://prove2.me/submissions/551a21d5-7c55-4e33-a93a-cb24ba7397b1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (A : ℕ → ℝ) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then A r else 0) ∂volume) =
      (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then A r else 0 ∂volume) := by
  intro δ
  have hfinite : volume (Ioo (0 : ℝ) (n : ℝ)) < ⊤ := by simp
  letI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (n : ℝ))) :=
    ⟨by simpa using hfinite⟩
  have hOuter (r : ℕ) :
      Integrable (fun t : ℝ =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then A r else 0) (volume.restrict (Ioo (0 : ℝ) (n : ℝ))) := by
    have hc : Integrable (fun _ : ℝ => A r)
        (volume.restrict (Ioo (0 : ℝ) (n : ℝ))) := integrable_const _
    have hEq :
        (fun t : ℝ =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then A r else 0) =
        (Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ)).indicator
          (fun _ : ℝ => A r) := by
      funext t
      simp only [Set.indicator, mem_Ico]
    rw [hEq]
    exact hc.indicator measurableSet_Ico
  rw [integral_finset_sum]
  intro r hr
  exact hOuter r
