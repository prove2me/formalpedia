-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_ae_fibrewise_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:20:36.899996+00:00
-- url     : https://prove2.me/submissions/d21b5456-807c-4d30-9f7e-7c8f97cd8da0

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_ae_stoppedEvent_measure_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped BigOperators ENNReal

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (τ : Ω → ι) (grid : Finset ι)
    (A E : Set Ω) (k : ℝ≥0∞)
    (hgrid : ∀ᵐ ω ∂μ, τ ω ∈ grid)
    (hAcell : ∀ s ∈ grid, MeasurableSet (A ∩ {ω : Ω | τ ω = s}))
    (hEcell : ∀ s ∈ grid, MeasurableSet (E ∩ {ω : Ω | τ ω = s}))
    (hfactor : ∀ s ∈ grid,
      μ (E ∩ {ω : Ω | τ ω = s}) =
        μ (A ∩ {ω : Ω | τ ω = s}) * k) :
    μ E = μ A * k := by
  classical
  calc
    μ E = ∑ s ∈ grid, μ (E ∩ {ω : Ω | τ ω = s}) :=
      finiteGrid_ae_stoppedEvent_measure_partition
        μ τ grid E hgrid hEcell
    _ = ∑ s ∈ grid, μ (A ∩ {ω : Ω | τ ω = s}) * k := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hfactor s hs
    _ = (∑ s ∈ grid, μ (A ∩ {ω : Ω | τ ω = s})) * k := by
      rw [Finset.sum_mul]
    _ = μ A * k := by
      rw [← finiteGrid_ae_stoppedEvent_measure_partition
        μ τ grid A hgrid hAcell]
