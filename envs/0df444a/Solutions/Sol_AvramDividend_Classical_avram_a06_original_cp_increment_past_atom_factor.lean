-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_increment_past_atom_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:26:10.754424+00:00
-- url     : https://prove2.me/submissions/90a2a200-4228-42eb-9239-0c9589d9c0f2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_zero_case
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_positive_case
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Assemble all count singleton factors from the zero and positive cases. -/
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
      ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = k} := by
  intro n t ht Z j v k
  cases k with
  | zero =>
      exact AvramDividend.Classical.avram_a06_original_cp_past_atom_zero_case
        P τ Y hd n t ht j v
  | succ k =>
      simpa only [Nat.succ_eq_add_one] using
        (AvramDividend.Classical.avram_a06_original_cp_past_atom_positive_case
          P τ Y hd n t ht j v k)
