-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a558_mean_budget_to_centred_L1_error_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:43:04.603829+00:00
-- url     : https://prove2.me/submissions/e9e3dc86-8142-41f6-835e-b0d8d926376e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (K : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hExpected : ∀ n, (∫ ω, F n ω ∂P) ≤ K) :
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ K + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by
  classical
  let M : ℕ → Ω → ℝ := fun n ω => F n ω - ∫ ξ, F n ξ ∂P
  let Err : ℕ → Ω → ℝ := fun _ _ => 0
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  refine ⟨M, Err, η, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [η]
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    constructor
    · exact (hInt n).sub (integrable_const _)
    · dsimp [M]
      rw [integral_sub (hInt n) (integrable_const _)]
      simp [integral_const]
  · intro n
    simp [Err]
  · intro n
    filter_upwards [] with ω
    dsimp [M, Err]
    have h := hExpected n
    simp only [max_self]
    linarith
  · intro n
    simp [Err, η] <;> positivity
