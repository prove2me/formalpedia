-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a246_integrable_combined_positive_source_small_large_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:32:38.531823+00:00
-- url     : https://prove2.me/submissions/1e71c1ca-a450-49f5-ae3a-3a9f27d5e9ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
  have hLow (m : ℕ) : 0 ≤ (∫ ω, F m ω ∂P) := by
    exact integral_nonneg (hFpos m)
  have hHi (m : ℕ) :
      (∫ ω, F m ω ∂P) ≤
        (∫ ω, S m ω ∂P) + (∫ ω, L m ω ∂P) := by
    calc
      _ ≤ ∫ ω, S m ω + L m ω ∂P :=
        integral_mono (hFI m) ((hSI m).add (hLI m)) (hPoint m)
      _ = (∫ ω, S m ω ∂P) + (∫ ω, L m ω ∂P) :=
        integral_add (hSI m) (hLI m)
  have ht : Tendsto (fun m =>
      (∫ ω, S m ω ∂P) + (∫ ω, L m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hSL.add hLL
  exact squeeze_zero hLow hHi ht
