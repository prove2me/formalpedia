-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:05:41.001204+00:00
-- url     : https://prove2.me/submissions/ff0623a5-8b50-48f3-96f8-af197feb1985

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original positive-stop finite-grid prefix inherits the tube noise bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m k : ℕ) (hk : k ≤ m + 1)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i ≤ k,
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      if i < k then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by
  let f : ℕ → ℝ := fun i =>
    Real.exp (-(q * (s i : ℝ))) *
      (X.X (s (i + 1)) ω - X.X (s i) ω -
        ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
  have hPrefix :=
    avram_gbB63_original_finitegrid_prefix_mask_equals_short_range m k hk f
  change |(Finset.range (m + 1)).sum (fun i => if i < k then f i else 0)| ≤ ε
  rw [hPrefix]
  cases k with
  | zero =>
      simpa using hε
  | succ j =>
      exact avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
        X ω j s hs hs0 hX0 q ε hq hε
        (fun i hi => hTube i hi)
