-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_original_stopped_L1_limit_zero_mean_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:16:20.785736+00:00
-- url     : https://prove2.me/submissions/82eec5ae-2763-4a4e-aff3-a0f9d61b922d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine L1 convergence and almost-everywhere limits inherit centred and zero-clock properties. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (σ : Ω → ℝ≥0) (Q : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hQI : ∀ n, Integrable (Q n) P) (hZI : Integrable Z P)
    (hQzero : ∀ᵐ ω ∂P, ∀ n, σ ω = 0 → Q n ω = 0)
    (hQmean : ∀ n, (∫ ω, Q n ω ∂P) = 0)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)))
    (hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => Q n ω) atTop (𝓝 (Z ω))) :
    (∫ ω, Z ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, σ ω = 0 → Z ω = 0 := by
  have hMean :
      (∫ ω, Z ω ∂P) = 0 := by
    have h :=
      AvramDividend.Classical.avram_gaussian12_restricted_L1_limit_preserves_zero_mean
        Set.univ MeasurableSet.univ Q hQI Z hZI
        (by intro n; simpa using hQmean n)
        (by simpa using hL1)
    simpa using h
  refine ⟨hMean, ?_⟩
  filter_upwards [hQzero, hPoint] with ω hzero hpoint
  intro hs
  have hconst : (fun n : ℕ => Q n ω) = fun _ => (0 : ℝ) := by
    funext n
    exact hzero n hs
  have htarget :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (Z ω)) := by
    simpa only [hconst] using hpoint
  exact (tendsto_nhds_unique tendsto_const_nhds htarget).symm
