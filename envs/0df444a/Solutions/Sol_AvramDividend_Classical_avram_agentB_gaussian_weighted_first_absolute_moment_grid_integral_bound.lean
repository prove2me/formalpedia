-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gaussian_weighted_first_absolute_moment_grid_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:01:45.755186+00:00
-- url     : https://prove2.me/submissions/df9ade2e-9f55-4c4d-a52d-9cd5b66b648c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Gaussian grid absolute weighted cell moments sum to at most
the physical conditional moment scale times total dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ)
    (a z : ℕ → Ω → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ Finset.range m, Integrable (a i) P)
    (haz : ∀ i ∈ Finset.range m,
      Integrable (fun ω => a i ω * |z i ω|) P)
    (hcell : ∀ i ∈ Finset.range m,
      (∫ ω, a i ω * |z i ω| ∂P) ≤
      δ * (∫ ω, a i ω ∂P))
    (hA : (∫ ω, ∑ i ∈ Finset.range m, a i ω ∂P) ≤ B) :
    (∫ ω, ∑ i ∈ Finset.range m,
      a i ω * |z i ω| ∂P) ≤ δ * B := by
  have hIntA : Integrable (fun ω => ∑ i ∈ Finset.range m, a i ω) P := by
    apply integrable_finset_sum
    intro i hi
    exact ha i hi
  have hIntAZ : Integrable (fun ω => ∑ i ∈ Finset.range m,
      a i ω * |z i ω|) P := by
    apply integrable_finset_sum
    intro i hi
    exact haz i hi
  have hS : (∑ i ∈ Finset.range m, (∫ ω, a i ω * |z i ω| ∂P)) ≤
      ∑ i ∈ Finset.range m, δ * (∫ ω, a i ω ∂P) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hcell i hi
  rw [integral_finset_sum (Finset.range m) ha] at hA
  rw [integral_finset_sum (Finset.range m) haz]
  calc
    (∑ i ∈ Finset.range m, ∫ ω, a i ω * |z i ω| ∂P) ≤
      ∑ i ∈ Finset.range m, δ * (∫ ω, a i ω ∂P) := hS
    _ = δ * ∑ i ∈ Finset.range m, (∫ ω, a i ω ∂P) := by
      simp only [Finset.mul_sum]
    _ ≤ δ * B := mul_le_mul_of_nonneg_left hA hδ
