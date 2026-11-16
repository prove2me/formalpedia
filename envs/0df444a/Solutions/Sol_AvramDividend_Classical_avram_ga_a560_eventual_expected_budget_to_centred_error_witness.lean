-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a560_eventual_expected_budget_to_centred_error_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:58:27.140436+00:00
-- url     : https://prove2.me/submissions/f0d40fc4-beae-4cdd-babf-311be5f9bfae

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
    (hExpected : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), (∫ ω, F n ω ∂P) ≤ K + ε) :
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
  let μ : ℕ → ℝ := fun n => ∫ ω, F n ω ∂P
  let β : ℕ → ℝ := fun n => max (μ n - K) 0
  let M : ℕ → Ω → ℝ := fun n ω => F n ω - μ n
  let Err : ℕ → Ω → ℝ := fun n _ => β n
  let η : ℕ → ℝ := fun n => β n + 1 / ((n : ℝ) + 1)
  have hβ0 (n : ℕ) : 0 ≤ β n := le_max_right _ _
  have hβ : Tendsto β atTop (nhds (0 : ℝ)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [] with n
      exact lt_of_lt_of_le ha (hβ0 n)
    · intro a ha
      filter_upwards [hExpected (a / 2) (half_pos ha)] with n hn
      have he : β n ≤ a / 2 := by
        dsimp [β, μ]
        apply max_le
        · linarith
        · linarith
      exact lt_of_le_of_lt he (half_lt_self ha)
  refine ⟨M, Err, η, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [η]
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hβ0 n]
  · simpa only [η, add_zero] using
      hβ.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    constructor
    · exact (hInt n).sub (integrable_const _)
    · dsimp [M, μ]
      rw [integral_sub (hInt n) (integrable_const _)]
      simp
  · intro n
    simp [Err]
  · intro n
    filter_upwards [] with ω
    have hbudget : μ n ≤ K + β n := by
      dsimp [β]
      have hh := le_max_left (μ n - K) (0 : ℝ)
      linarith
    dsimp [M, Err]
    rw [max_eq_left (hβ0 n)]
    linarith
  · intro n
    dsimp [Err, η]
    rw [max_eq_left (hβ0 n)]
    simp <;> positivity
