-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_stationary_increment_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:52:18.705916+00:00
-- url     : https://prove2.me/submissions/e4e560b2-a492-4803-9eaf-28bbb0148978

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_nat_identDistrib_of_tail
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_tail_probability_stationary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Original count stationarity follows from its strict tails and count measurability. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ) -
        LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))
      (fun ω => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (k : ℝ) -
        LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)) P P := by
  let N : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ → ℕ :=
    fun ω u => LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) u
  let X := fun ω => N ω (s + k : ℝ) - N ω (s : ℝ)
  let Z := fun ω => N ω (k : ℝ) - N ω 0
  have hτ (n : ℕ) : Measurable (τ n) := hd.measurable_interarrival n
  have hN (u : ℝ) : Measurable (fun ω => N ω u) :=
    AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public τ hτ u
  have hX : Measurable X := (hN (s + k : ℝ)).sub (hN (s : ℝ))
  have hZ : Measurable Z := (hN (k : ℝ)).sub (hN 0)
  have hTail (m : ℕ) :
      P {ω | m < X ω} = P {ω | m < Z ω} :=
    AvramDividend.Classical.avram_a06_original_cp_increment_tail_probability_stationary
      P τ Y hd s k m
  change IdentDistrib X Z P P
  exact AvramDividend.Classical.avram_a06_nat_identDistrib_of_tail
    P X Z hX hZ hTail
