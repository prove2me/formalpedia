-- Prove2me | solution 1 for DataDrivenRO.KS.theta_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:18:38.284992+00:00
-- url     : https://prove2.me/submissions/41b89088-921b-4ed5-8a56-8209ab9da1d4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

open DataDrivenRO.KS in
theorem b95d1723_mix_sum (N : ℕ) (Γ θ : ℝ) (w : Fin (N + 2) → ℝ) :
    ∑ j, mix N Γ θ j * w j
      = θ * (∑ j, qL N Γ j * w j) + (1 - θ) * (∑ j, qR N Γ j * w j) := by
  simp only [mix, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

open DataDrivenRO.KS in
theorem solution (N : ℕ) (Γ : ℝ) (w : Fin (N + 2) → ℝ) :
    IsGreatest ((fun θ : ℝ => ∑ j, mix N Γ θ j * w j) '' Set.Icc 0 1)
      (max (∑ j, qL N Γ j * w j) (∑ j, qR N Γ j * w j)) := by
  set A := ∑ j, qL N Γ j * w j
  set B := ∑ j, qR N Γ j * w j
  constructor
  · rcases le_total A B with h | h
    · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      simp only [b95d1723_mix_sum]
      rw [max_eq_right h]; ring
    · refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_⟩
      simp only [b95d1723_mix_sum]
      rw [max_eq_left h]; ring
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [b95d1723_mix_sum]
    have hA : A ≤ max A B := le_max_left _ _
    have hB : B ≤ max A B := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hA h0, mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr h1)]
