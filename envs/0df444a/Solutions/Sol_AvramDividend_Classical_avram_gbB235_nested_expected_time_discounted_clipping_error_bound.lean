-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB235_nested_expected_time_discounted_clipping_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:16.212016+00:00
-- url     : https://prove2.me/submissions/f35ed40d-64f6-4b2c-a5a8-2ca4b6704607

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Nested time and sample integrals preserve the discounted strip-square bound. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (w : ℝ → ℝ) (a a' b' b B q : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hq : 0 ≤ q)
    (Y : α → β → ℝ) (t : α → ℝ) (ht : ∀ s, 0 ≤ t s) :
    let G : α → β → ℝ := fun s ω =>
      (Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a b then deriv w (Y s ω) else 1) -
        Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a' b' then deriv w (Y s ω) else 1))^2
    let J : α → β → ℝ := fun s ω =>
      4 * B^2 *
        (if Y s ω ∈ Set.Icc a a' ∨ Y s ω ∈ Set.Icc b' b
          then (1 : ℝ) else 0)
    (∀ s, Integrable (G s) ν) →
    (∀ s, Integrable (J s) ν) →
    Integrable (fun s => ∫ ω, G s ω ∂ν) μ →
    Integrable (fun s => ∫ ω, J s ω ∂ν) μ →
    (∫ s, (∫ ω, G s ω ∂ν) ∂μ) ≤
      (∫ s, (∫ ω, J s ω ∂ν) ∂μ) := by
  intro G J hG hJ hGO hJO
  have hInner (s : α) :
      (∫ ω, G s ω ∂ν) ≤ (∫ ω, J s ω ∂ν) := by
    apply integral_mono (hG s) (hJ s)
    intro ω
    simpa only [G, J] using
      (avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
        w a a' b' b B q (t s) ha hab hb hB hgrad hq
        (ht s) (Y s ω))
  exact integral_mono hGO hJO hInner
