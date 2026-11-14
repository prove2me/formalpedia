-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a99_true_gaussian_stop_crossing_random_L1_envelope_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:34.195423+00:00
-- url     : https://prove2.me/submissions/e57a8bab-fd45-4546-a951-364dc35e8f26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- A genuine at-most-one-cell random crossing envelope with vanishing expected size controls positive L1 without mesh multiplicity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Ω → Finset ℕ) (f : ℕ → ℕ → Ω → ℝ)
    (B : ℕ → Ω → ℝ)
    (hCard : ∀ m ω, (S m ω).card ≤ 1)
    (hBn : ∀ m ω, 0 ≤ B m ω)
    (hBI : ∀ m, Integrable (B m) P)
    (hFI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m ω, max (f m i ω) 0) P)
    (hCell : ∀ m ω i, i ∈ S m ω → max (f m i ω) 0 ≤ B m ω)
    (hBLim : Tendsto (fun m => ∫ ω, B m ω ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, (∑ i ∈ S m ω, max (f m i ω) 0) ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  let F : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m ω, max (f m i ω) 0
  change Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ))
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ F m ω := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_max_right (f m i ω) 0
  have hBound (m : ℕ) (ω : Ω) : F m ω ≤ B m ω := by
    change (∑ i ∈ S m ω, max (f m i ω) 0) ≤ B m ω
    exact avram_ga_a97_single_crossing_positive_error_finset_bound
      (S m ω) (fun i => f m i ω) (B m ω)
      (hBn m ω) (hCard m ω) (hCell m ω)
  have hIntegralPos (m : ℕ) :
      0 ≤ (∫ ω, F m ω ∂P) := integral_nonneg (hPos m)
  have hIntegralBound (m : ℕ) :
      (∫ ω, F m ω ∂P) ≤ (∫ ω, B m ω ∂P) :=
    integral_mono (hFI m) (hBI m) (hBound m)
  exact squeeze_zero hIntegralPos hIntegralBound hBLim
