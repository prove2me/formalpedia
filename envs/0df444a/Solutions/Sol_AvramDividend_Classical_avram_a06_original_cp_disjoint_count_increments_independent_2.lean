-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_cp_disjoint_count_increments_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:48:05.486373+00:00
-- url     : https://prove2.me/submissions/c120f79a-6ad1-4e73-80dc-2f30ceba218f

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_increment_joint_atomic_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_nat_family_independent_of_atomic_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Independence of count increments follows from their joint atomic product law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndepFun (fun (i : Fin n) ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) P := by
  intro n t ht
  let Z : Fin n → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ := fun i ω =>
    LevyFoundations.jumpCount
      (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
    LevyFoundations.jumpCount
      (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)
  obtain ⟨hMeas, hAtoms⟩ :=
    AvramDividend.Classical.avram_a06_original_cp_count_increment_joint_atomic_product
      P τ Y hd n t ht
  change iIndepFun Z P
  apply AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
    P n Z
  · exact hMeas
  · exact hAtoms
