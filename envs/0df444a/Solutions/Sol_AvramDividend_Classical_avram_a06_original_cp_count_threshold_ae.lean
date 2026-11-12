-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:13:51.366195+00:00
-- url     : https://prove2.me/submissions/fd65892c-b037-4b08-ada3-0226a262a69d

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_levy_foundations_jumpCountLtIff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal
noncomputable section

/-- The original renewal count is exactly the count of completed waiting-time
    prefixes at every horizon, outside one joint null set. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ (u : ℝ) (n : ℕ),
      n < LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) u ↔
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ u := by
  have hmono := levy_foundations_compoundDriverArrivalStrictMono hd (by norm_num)
  have htop := levy_foundations_compoundDriverArrivalDiverges hd (by norm_num)
  filter_upwards [hmono, htop] with ω hm ht
  intro u n
  simpa [LevyFoundations.arrival] using
    (levy_foundations_jumpCountLtIff
      (fun j => LevyFoundations.arrival τ j ω) hm ht n u)
