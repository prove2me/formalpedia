-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_increment_joint_atomic_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:32:16.203656+00:00
-- url     : https://prove2.me/submissions/4161046d-6b49-48f2-ad74-613935fcc8f7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_finite_nat_atomic_chain_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_step_atom_factor
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Separate original one-step renewal factorisation from finite telescoping. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      (∀ i : Fin n, Measurable (fun ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ))) ∧
      ∀ v : Fin n → ℕ,
        P {ω | ∀ i : Fin n,
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
           LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) = v i} =
        ∏ i : Fin n, P {ω |
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
           LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) = v i} := by
  intro n t ht
  let Z : Fin n → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ := fun i ω =>
    LevyFoundations.jumpCount
      (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
    LevyFoundations.jumpCount
      (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)
  obtain ⟨hMeas, hStep⟩ :=
    AvramDividend.Classical.avram_a06_original_cp_increment_step_atom_factor
      P τ Y hd n t ht
  constructor
  · intro i
    exact hMeas i
  · intro v
    simpa [Z] using
      (AvramDividend.Classical.avram_a06_generic_finite_nat_atomic_chain_product
        P n Z hStep v)
