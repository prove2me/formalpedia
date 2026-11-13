-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_cp_original_noarrival_positive_event_raw_linear_source_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:26:10.933834+00:00
-- url     : https://prove2.me/submissions/15e10a37-6c1a-4341-a331-029f9cf64526

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P ∧
      0 < P {ω | (1 / 10 : ℝ) < τ 0 ω} ∧
      (∀ ω, (1 / 10 : ℝ) < τ 0 ω →
        ∀ t : ℝ, t ≤ 1 / 10 →
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω = t)  := by
  obtain ⟨P, τ, Y, hProb, hd⟩ :=
    avram_a06_uniform_driver_on_real_sequence_product
  letI : IsProbabilityMeasure P := hProb
  refine ⟨P, τ, Y, hProb, hd, ?_, ?_⟩
  · rw [avram_a06_original_cp_interarrival_survival
      P τ Y hd 0 (1 / 10) (by norm_num)]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · intro ω hw t ht
    have ht0 : t < τ 0 ω := lt_of_le_of_lt ht hw
    have hmem :
        (0 : ℕ) ∈ {n : ℕ | t < LevyFoundations.arrival τ n ω} := by
      simpa [LevyFoundations.arrival] using ht0
    have hcount :
        LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) t = 0 := by
      unfold LevyFoundations.jumpCount
      exact Nat.eq_zero_of_le_zero (Nat.sInf_le hmem)
    simpa [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath,
      hcount]
