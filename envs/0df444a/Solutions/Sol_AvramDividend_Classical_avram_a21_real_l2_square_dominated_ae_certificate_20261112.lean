-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_real_l2_square_dominated_ae_certificate_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:21:38.592877+00:00
-- url     : https://prove2.me/submissions/b05f7da0-9c5c-455f-9121-9080ad2e496e

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- A common square-integrable real envelope certifies uniform a.e.
squared domination and square convergence of a sequence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (C B : Ω → ℝ)
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P)
    (hB2 : Integrable (fun ω => (B ω)^2) P)
    (hBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (C ω))) :
    (∀ k, AEStronglyMeasurable (fun ω => (F k ω)^2) P) ∧
      Integrable (fun ω => (B ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖(F k ω)^2‖ ≤ (B ω)^2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => (F k ω)^2)
        atTop (𝓝 ((C ω)^2))) := by
  constructor
  · intro k
    exact (hFmeas k).pow 2
  constructor
  · exact hB2
  constructor
  · intro k
    filter_upwards [hBound] with ω hω
    have hk := hω k
    have hn : 0 ≤ B ω := le_trans (norm_nonneg _) hk
    rw [norm_pow]
    have hm : 0 ≤ (B ω - ‖F k ω‖) * (B ω + ‖F k ω‖) :=
      mul_nonneg (sub_nonneg.mpr hk)
        (add_nonneg hn (norm_nonneg _))
    nlinarith
  · filter_upwards [hLimit] with ω hω
    exact hω.pow 2
