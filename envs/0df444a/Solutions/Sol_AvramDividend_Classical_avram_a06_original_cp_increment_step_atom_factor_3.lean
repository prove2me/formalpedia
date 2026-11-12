-- Prove2me | solution 3 for AvramDividend.Classical.avram_a06_original_cp_increment_step_atom_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:34:22.225637+00:00
-- url     : https://prove2.me/submissions/cfd08e20-9678-4721-8621-377f7782cd32

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_grid_count_increment_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_past_atom_factor
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Combine source-level measurability with the finite count-atom factorisation. -/
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
  dsimp
  constructor
  · intro i
    exact AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
      P τ Y hd n t ht i
  · exact AvramDividend.Classical.avram_a06_original_cp_increment_past_atom_factor
      P τ Y hd n t ht
