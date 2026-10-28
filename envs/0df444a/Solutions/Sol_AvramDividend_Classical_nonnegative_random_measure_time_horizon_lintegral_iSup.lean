-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_random_measure_time_horizon_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:07:16.360386+00:00
-- url     : https://prove2.me/submissions/ad1b2de7-4379-46a4-9f58-6aba48873716

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_nonnegative_time_horizon_lintegral_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical ENNReal
open AvramDividend.Classical

/-- The expected dividend integral for a random measure is the supremum of expected finite-horizon integrals, given the needed measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℝ)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ ω, Measurable (f ω))
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in Icc (0 : ℝ) (n : ℝ), f ω t ∂(μ ω))) :
    (∫⁻ ω, (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) ∂P) =
      ⨆ n : ℕ, (∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        f ω t ∂(μ ω)) ∂P) := by
  have hmono : Monotone (fun n : ℕ => fun ω : Ω =>
      ∫⁻ t in Icc (0 : ℝ) (n : ℝ), f ω t ∂(μ ω)) := by
    intro n m hnm ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (by exact_mod_cast hnm)⟩
  have hpoint : ∀ ω : Ω,
      (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) =
        ⨆ n : ℕ, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
          f ω t ∂(μ ω)) := by
    intro ω
    exact nonnegative_time_horizon_lintegral_iSup (μ ω) (f ω) (hf ω)
  calc
    (∫⁻ ω, (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) ∂P) =
        (∫⁻ ω, (⨆ n : ℕ, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
          f ω t ∂(μ ω))) ∂P) := by
      simp_rw [hpoint]
    _ = ⨆ n : ℕ, (∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
      f ω t ∂(μ ω)) ∂P) := lintegral_iSup hMeas hmono
