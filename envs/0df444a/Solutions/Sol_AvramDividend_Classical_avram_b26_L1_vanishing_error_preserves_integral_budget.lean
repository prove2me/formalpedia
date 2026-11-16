-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_L1_vanishing_error_preserves_integral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:46:26.477176+00:00
-- url     : https://prove2.me/submissions/e35699ad-9cff-443e-8e57-a75be86c349e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y B : Ω → ℝ)
    (M E : ℕ → Ω → ℝ)
    (hY : Integrable Y μ) (hB : Integrable B μ)
    (hM : ∀ n, Integrable (M n) μ)
    (hE : ∀ n, Integrable (E n) μ)
    (hMmean : ∀ n, (∫ ω, M n ω ∂μ) = 0)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂μ) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂μ,
      Y ω ≤ B ω + M n ω + E n ω) :
    (∫ ω, Y ω ∂μ) ≤ (∫ ω, B ω ∂μ) := by
  have hUpper (n : ℕ) :
      (∫ ω, Y ω ∂μ) ≤
        (∫ ω, B ω ∂μ) + (∫ ω, ‖E n ω‖ ∂μ) := by
    have hI : Integrable (fun ω => B ω + M n ω + E n ω) μ :=
      (hB.add (hM n)).add (hE n)
    have hCashI :
        (∫ ω, Y ω ∂μ) ≤
          (∫ ω, B ω + M n ω + E n ω ∂μ) :=
      integral_mono_ae hY hI (hCash n)
    have hErrI :
        (∫ ω, E n ω ∂μ) ≤ (∫ ω, ‖E n ω‖ ∂μ) := by
      apply integral_mono (hE n) (hE n).norm
      intro ω
      simpa [Real.norm_eq_abs] using (le_abs_self (E n ω))
    calc
      (∫ ω, Y ω ∂μ) ≤
          (∫ ω, B ω + M n ω + E n ω ∂μ) := hCashI
      _ = (∫ ω, B ω ∂μ) + (∫ ω, M n ω ∂μ) +
          (∫ ω, E n ω ∂μ) := by
          calc
            (∫ ω, B ω + M n ω + E n ω ∂μ) =
                (∫ ω, B ω + M n ω ∂μ) +
                (∫ ω, E n ω ∂μ) := by
              exact integral_add (hB.add (hM n)) (hE n)
            _ = (∫ ω, B ω ∂μ) + (∫ ω, M n ω ∂μ) +
                (∫ ω, E n ω ∂μ) := by
              rw [integral_add hB (hM n)]
      _ = (∫ ω, B ω ∂μ) + (∫ ω, E n ω ∂μ) := by
          rw [hMmean n]
          ring
      _ ≤ (∫ ω, B ω ∂μ) + (∫ ω, ‖E n ω‖ ∂μ) := by
          linarith [hErrI]
  by_contra h
  have hpos :
      0 < (∫ ω, Y ω ∂μ) - (∫ ω, B ω ∂μ) := by
    linarith
  have hevent :
      ∀ᶠ n in atTop,
        (∫ ω, ‖E n ω‖ ∂μ) <
          (∫ ω, Y ω ∂μ) - (∫ ω, B ω ∂μ) := by
    exact hEL1.eventually (Iio_mem_nhds hpos)
  obtain ⟨n, hn⟩ := hevent.exists
  have hbound := hUpper n
  linarith
