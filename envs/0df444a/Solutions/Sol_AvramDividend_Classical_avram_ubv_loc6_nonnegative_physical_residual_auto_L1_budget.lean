-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:18:03.130809+00:00
-- url     : https://prove2.me/submissions/04b64e56-0101-441a-afa1-0002b40d436e

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

noncomputable section

/-- The original localised Itô residual supplies L1 of the nonnegative
paid payoff as well as its HJB expectation budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F M : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMint : Integrable M P)
    (hSource : ∀ᵐ ω ∂P, F ω ≤ b + M ω)
    (hMmean : (∫ ω, M ω ∂P) ≤ 0) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤ b := by
  have hMajorant : Integrable (fun ω => b + M ω) P :=
    (integrable_const b).add hMint
  have hFint : Integrable F P := by
    apply Integrable.mono' hMajorant hFmeas
    filter_upwards [hFnonneg, hSource] with ω hnonneg hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  refine ⟨hFint, ?_⟩
  have hIntegral := integral_mono_ae hFint hMajorant hSource
  calc
    (∫ ω, F ω ∂P) ≤ (∫ ω, b + M ω ∂P) := hIntegral
    _ = b + (∫ ω, M ω ∂P) := by
      simp [integral_add, hMint]
    _ ≤ b := by linarith only [hMmean]
