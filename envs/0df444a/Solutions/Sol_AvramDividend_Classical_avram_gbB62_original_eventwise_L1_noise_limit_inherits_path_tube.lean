-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:02:36.144229+00:00
-- url     : https://prove2.me/submissions/952f824c-08ca-4ece-88c1-8fb7fcd7f7b2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section
/-- A restricted Gaussian grid limit inherits a tube bound on the original event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hBound : ∀ m ω, ω ∈ A → |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  let M' : ℕ → Ω → ℝ := fun m => A.indicator (M m)
  let N' : Ω → ℝ := A.indicator N
  have hE : ∀ᵐ ω ∂(P.restrict A), ω ∈ A := ae_restrict_mem hA
  have hNI' : Integrable N' (P.restrict A) := hNI.indicator hA
  have hMI' : ∀ m, Integrable (M' m) (P.restrict A) := by
    intro m
    exact (hMI m).indicator hA
  have hBound' : ∀ m ω, |M' m ω| ≤ ε := by
    intro m ω
    by_cases hω : ω ∈ A
    · simpa [M', Set.indicator_of_mem hω] using hBound m ω hω
    · simp [M', Set.indicator_of_notMem hω, hε]
  have hDiff (m : ℕ) :
      (∫ ω, |N' ω - M' m ω| ∂(P.restrict A)) =
      (∫ ω in A, |N ω - M m ω| ∂P) := by
    apply integral_congr_ae
    filter_upwards [hE] with ω hω
    simp [N', M', Set.indicator_of_mem hω]
  have hL1' : Tendsto (fun m =>
      ∫ ω, |N' ω - M' m ω| ∂(P.restrict A))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hDiff] using hL1
  have hLimit :=
    avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
      (P.restrict A) N' M' ε hε hNI' hMI' hBound' hL1'
  filter_upwards [hLimit, hE] with ω hω hωA
  simpa [N', Set.indicator_of_mem hωA] using hω
