-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:47:49.319293+00:00
-- url     : https://prove2.me/submissions/7df66055-6ebf-496e-bf5b-d8d2ae1f7fd3

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℋ : MeasurableSpace Ω) (hℋ : ℋ ≤ mΩ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hUpper : ∀ᵐ ω ∂P, P[F | ℋ] ω ≤ b) :
    ∃ MG MJ B : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      P[MG | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      P[MJ | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      (∀ᵐ ω ∂P, B ω ≤ 0) ∧
      (∀ ω, F ω = b + MG ω + MJ ω + B ω) := by
  classical
  let C : Ω → ℝ := P[F | ℋ]
  let MG : Ω → ℝ := fun ω => F ω - C ω
  let MJ : Ω → ℝ := fun _ => 0
  let B : Ω → ℝ := fun ω => C ω - b
  have hCI : Integrable C P := integrable_condExp
  have hCenter : P[MG | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hSub : P[(F - C) | ℋ] =ᵐ[P] P[F | ℋ] - P[C | ℋ] :=
      condExp_sub hFI hCI ℋ
    have hId : P[C | ℋ] =ᵐ[P] C := by
      change P[P[F | ℋ] | ℋ] =ᵐ[P] P[F | ℋ]
      exact condExp_condExp_of_le le_rfl hℋ
    filter_upwards [hSub, hId] with ω hs hi
    change P[(F - C) | ℋ] ω = 0
    calc
      P[(F - C) | ℋ] ω = (P[F | ℋ] - P[C | ℋ]) ω := hs
      _ = 0 := by simp only [Pi.sub_apply, hi, C, sub_self]
  have hMJI : Integrable MJ P := by
    have hz : Integrable (fun ω => F ω - F ω) P := hFI.sub hFI
    simpa only [MJ, sub_self] using hz
  refine ⟨MG, MJ, B, hFI.sub hCI, hMJI,
    hCenter, ?_, ?_, ?_⟩
  · simpa [MJ] using (condExp_zero (m := ℋ) (μ := P))
  · filter_upwards [hUpper] with ω hω
    dsimp [B, C]
    linarith
  · intro ω
    dsimp [MG, MJ, B, C]
    ring
