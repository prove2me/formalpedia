-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_disjoint_count_increments_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:19:02.746612+00:00
-- url     : https://prove2.me/submissions/ca4cb0f6-e7f7-4079-8ade-6c3716eb6533

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_nat_family_independent_of_atomic_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_increment_joint_atomic_product
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Reduce original count independence to joint atom laws and a discrete independence theorem. -/
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
  have hAtoms :=
    AvramDividend.Classical.avram_a06_original_cp_count_increment_joint_atomic_product
      P τ Y hd n t ht
  exact AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
    P n
    (fun (i : Fin n) ω =>
      LevyFoundations.jumpCount
        (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
      LevyFoundations.jumpCount
        (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ))
    hAtoms.1 hAtoms.2
