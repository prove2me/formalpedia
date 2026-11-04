-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_integral_poly_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:27:24.016796+00:00
-- url     : https://prove2.me/submissions/a4f6a2cd-bae7-47fb-b4f8-6fc1a74826a3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (μ : Measure ℝ) (g : ℝ → ℝ) (p : Polynomial ℝ)
    (ε : ℝ) (K : ℕ)
    (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (hbound : ∀ z : ℝ, 0 ≤ z →
      |g z - p.eval z| ≤ ε * (1 + z ^ K))
    (hg : Integrable g μ)
    (hp : Integrable (fun z : ℝ => p.eval z) μ)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (hK : Integrable (fun z : ℝ => z ^ K) μ) :
    |(∫ z : ℝ, g z ∂μ) - (∫ z : ℝ, p.eval z ∂μ)| ≤
      ε * ((∫ _ : ℝ, (1 : ℝ) ∂μ) +
        (∫ z : ℝ, z ^ K ∂μ)) := by
  have hdiff : Integrable (fun z : ℝ => g z - p.eval z) μ :=
    hg.sub hp
  have habs : Integrable (fun z : ℝ => |g z - p.eval z|) μ :=
    hdiff.abs
  have hplus : Integrable (fun z : ℝ => (1 : ℝ) + z ^ K) μ :=
    hOne.add hK
  have henv : Integrable (fun z : ℝ => ε * (1 + z ^ K)) μ :=
    hplus.const_mul ε
  have hae : ∀ᵐ z ∂μ,
      |g z - p.eval z| ≤ ε * (1 + z ^ K) :=
    hpositive.mono (fun z hz => hbound z hz)
  have hmono :
      (∫ z : ℝ, |g z - p.eval z| ∂μ) ≤
        (∫ z : ℝ, ε * (1 + z ^ K) ∂μ) :=
    integral_mono_ae habs henv hae
  calc
    |(∫ z : ℝ, g z ∂μ) - (∫ z : ℝ, p.eval z ∂μ)| =
        |∫ z : ℝ, g z - p.eval z ∂μ| := by
          rw [integral_sub hg hp]
    _ ≤ ∫ z : ℝ, |g z - p.eval z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : ℝ, ε * (1 + z ^ K) ∂μ := hmono
    _ = ε * ((∫ _ : ℝ, (1 : ℝ) ∂μ) +
        (∫ z : ℝ, z ^ K ∂μ)) := by
          rw [integral_const_mul, integral_add hOne hK]
