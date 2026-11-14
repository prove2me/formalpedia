-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a127_original_gaussian_random_crossing_HJB_compensator_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:42.394124+00:00
-- url     : https://prove2.me/submissions/fd88e28f-bc3e-4d50-bf56-78852b2d2db5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Original true random Gaussian physical crossing HJB compensation has vanishing expected L1 under its integrable finite-horizon source envelope. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z Δ H : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hΔ : ∀ m ω, 0 ≤ Δ m ω)
    (hError : ∀ m ω,
      |H m ω| ≤ K * (|Z m ω| + (Z m ω)^2 + Δ m ω))
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun m => Z m ω) atTop (𝓝 (0 : ℝ)))
    (hΔlim : ∀ᵐ ω ∂P, Tendsto (fun m => Δ m ω) atTop (𝓝 (0 : ℝ)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => |H m ω|) P)
    (hDom : ∀ m, ∀ᵐ ω ∂P, |H m ω| ≤ B ω) :
    Tendsto (fun m => ∫ ω, |H m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hAE : ∀ᵐ ω ∂P, Tendsto (fun m => H m ω)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hZ, hΔlim] with ω hz hd
    exact avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
      (fun m => Z m ω) (fun m => Δ m ω)
      (fun m => H m ω) K hK (fun m => hΔ m ω)
      (fun m => hError m ω) hz hd
  have hAbs : ∀ᵐ ω ∂P, Tendsto (fun m => |H m ω|)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAE] with ω h
    simpa only [abs_zero] using h.abs
  have hB (m : ℕ) : ∀ᵐ ω ∂P, ‖|H m ω|‖ ≤ B ω := by
    filter_upwards [hDom m] with ω hd
    simpa only [Real.norm_eq_abs, abs_abs] using hd
  have h := tendsto_integral_of_dominated_convergence
    B hMeas hBI hB hAbs
  simpa only [integral_zero] using h
