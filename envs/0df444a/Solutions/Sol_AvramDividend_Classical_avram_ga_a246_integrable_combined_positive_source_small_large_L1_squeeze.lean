-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a246_integrable_combined_positive_source_small_large_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:21.970201+00:00
-- url     : https://prove2.me/submissions/6268eb63-7405-4dcf-9fbb-dfe81b761e7c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S L : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hSI : ∀ m, Integrable (S m) P)
    (hLI : ∀ m, Integrable (L m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hPoint : ∀ m ω, F m ω ≤ S m ω + L m ω)
    (hSL : Tendsto (fun m => ∫ ω, S m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hLL : Tendsto (fun m => ∫ ω, L m ω ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  apply avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
    P F S L 1 (by norm_num) hFI hSI hLI hFpos
  · intro m ω
    simpa using hPoint m ω
  · exact hSL
  · exact hLL
