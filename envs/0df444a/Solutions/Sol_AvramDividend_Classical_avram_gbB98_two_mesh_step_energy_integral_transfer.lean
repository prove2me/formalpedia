-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB98_two_mesh_step_energy_integral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:16:28.268409+00:00
-- url     : https://prove2.me/submissions/ccacc186-2c77-42ac-b989-3797e335db70

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB96_two_mesh_squared_step_pointwise
import Theorems.Thm_AvramDividend_Classical_avram_gbB85_integral_expected_finite_step_kernel
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n m p : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ r, Integrable (fun ω =>
      (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) ^ 2) P) :
    let N : ℕ := (m + 1) * (p + 1)
    let step : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (K m t ω - K p t ω) ^ 2 ∂P) ∂volume) =
    step * (Finset.range N).sum (fun r =>
      ∫ ω, (G m (r / (p + 1)) ω -
        G p (r / (m + 1)) ω) ^ 2 ∂P) := by
  intro N step K
  let F : ℕ → Ω → ℝ := fun r ω =>
    (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  have hF' : ∀ r, Integrable (F r) P := hF
  have hTime :
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω - K p t ω) ^ 2 ∂P) ∂volume) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (Finset.range N).sum (fun r =>
          if (r : ℝ) * step ≤ t ∧
            t < ((r + 1 : ℕ) : ℝ) * step
          then F r ω else 0) ∂P) ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    apply integral_congr_ae
    filter_upwards [] with ω
    exact avram_gbB96_two_mesh_squared_step_pointwise
      n m p hn G t ht ω
  have hKernel :=
    avram_gbB85_integral_expected_finite_step_kernel
      P n N hn hN F hF'
  calc
    _ = (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (Finset.range N).sum (fun r =>
            if (r : ℝ) * step ≤ t ∧
              t < ((r + 1 : ℕ) : ℝ) * step
            then F r ω else 0) ∂P) ∂volume) := hTime
    _ = _ := by simpa only [step, F] using hKernel
