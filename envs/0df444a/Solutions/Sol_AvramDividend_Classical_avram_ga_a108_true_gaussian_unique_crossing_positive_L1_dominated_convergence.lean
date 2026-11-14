-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:45:30.936105+00:00
-- url     : https://prove2.me/submissions/0745137b-f77d-494f-b937-1be67109b31d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Original Gaussian single random crossing-cell positive spatial error is L1-small under its genuine uniform integrable envelope and a.s. decay. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Ω → Finset ℕ) (f : ℕ → ℕ → Ω → ℝ)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hCard : ∀ᵐ ω ∂P, ∀ m, (S m ω).card ≤ 1)
    (hPoint : ∀ᵐ ω ∂P, ∀ m i, i ∈ S m ω →
      max (f m i ω) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ S m ω, max (f m i ω) 0) P)
    (hAE : ∀ᵐ ω ∂P, Tendsto
      (fun m => ∑ i ∈ S m ω, max (f m i ω) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (∑ i ∈ S m ω, max (f m i ω) 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let F : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m ω, max (f m i ω) 0
  have hNonneg (m : ℕ) (ω : Ω) : 0 ≤ F m ω := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro i hi
    exact le_max_right (f m i ω) 0
  have hDom (m : ℕ) : ∀ᵐ ω ∂P, ‖F m ω‖ ≤ B ω := by
    filter_upwards [hB, hCard, hPoint] with ω hPos hOne hBound
    have hUpper := avram_ga_a97_single_crossing_positive_error_finset_bound
      (S m ω) (fun i => f m i ω) (B ω)
      hPos (hOne m) (hBound m)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hNonneg m ω)] using hUpper
  have hT := tendsto_integral_of_dominated_convergence
    B hMeas hBI hDom hAE
  simpa only [integral_zero] using hT
