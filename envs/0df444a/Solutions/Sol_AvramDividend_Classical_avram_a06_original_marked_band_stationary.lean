-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_marked_band_stationary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:59:22.986088+00:00
-- url     : https://prove2.me/submissions/353b5e5d-aeff-4abc-9e9d-020596062260
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_random_index_shift
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_count_law_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Stationarity of the original marked Poisson band follows by shifting random-index
    marks to a fresh prefix and transporting the stationary count increment law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)), Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ))
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (k : ℝ)), Y j ω)
      P P := by
  exact
    (AvramDividend.Classical.avram_a06_original_marked_band_random_index_shift
      P τ Y hd s k).trans
    (AvramDividend.Classical.avram_a06_original_marked_band_count_law_transfer
      P τ Y hd s k)
