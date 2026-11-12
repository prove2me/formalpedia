-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_cp_increment_step_atom_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:29:09.499611+00:00
-- url     : https://prove2.me/submissions/2c8ed00f-101d-4075-b140-6a76886ce127

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_zero_case
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_positive_case
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      let Z : Fin n → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
        fun i ω => LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.castSucc : ℝ)
      (∀ i, Measurable (Z i)) ∧
      ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = k} := by
  intro n t ht
  constructor
  · intro i
    have ha := avram_a06_compound_jumpCount_measurable_public
      τ hd.measurable_interarrival (t i.succ : ℝ)
    have hb := avram_a06_compound_jumpCount_measurable_public
      τ hd.measurable_interarrival (t i.castSucc : ℝ)
    exact ha.sub hb
  · intro j v k
    cases k with
    | zero =>
        exact avram_a06_original_cp_past_atom_zero_case
          P τ Y hd n t ht j v
    | succ k =>
        exact avram_a06_original_cp_past_atom_positive_case
          P τ Y hd n t ht j v k
