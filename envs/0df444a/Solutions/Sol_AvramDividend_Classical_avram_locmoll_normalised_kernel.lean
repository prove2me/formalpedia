-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_normalised_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:36.638002+00:00
-- url     : https://prove2.me/submissions/73467067-5b6a-455d-a915-86c5ba393021

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ → ℝ,
      Integrable ρ ∧ (∫ r, ρ r) = 1 ∧
      (0 ≤ᵐ[volume] ρ) ∧
      (∀ᵐ r ∂volume, ρ r ≠ 0 →
        r ∈ Icc (δ / 3) (2 * (δ / 3))) ∧
      ContDiff ℝ 2 ρ ∧ HasCompactSupport ρ := by 
  let f : ContDiffBump (δ / 2) :=
    ⟨δ / 12, δ / 6, by linarith, by linarith⟩
  refine ⟨f.normed volume, f.integrable_normed, f.integral_normed,
    Filter.Eventually.of_forall (fun r => f.nonneg_normed r), ?_,
    f.contDiff_normed, f.hasCompactSupport_normed⟩
  filter_upwards [] with r hr
  have hs : r ∈ Function.support (f.normed volume) := hr
  rw [f.support_normed_eq] at hs
  have hh : dist r (δ / 2) < δ / 6 := hs
  rw [Real.dist_eq] at hh
  obtain ⟨hl, hu⟩ := abs_lt.mp hh
  exact ⟨by linarith, by linarith⟩
