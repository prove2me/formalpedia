-- Prove2me | solution 1 for AvramDividend.Classical.eventually_quadratic_lower_gt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:38:30.173958+00:00
-- url     : https://prove2.me/submissions/1f72b8e2-09d6-4cac-af68-e6043fe4f521

import Mathlib

theorem solution
    (A b D q : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ θ : ℝ, B ≤ θ → q < A * θ ^ 2 + b * θ - D := by
  let E : ℝ := |b| + |D| + |q| + 2
  let B : ℝ := max 1 (E / A)
  refine ⟨B, ?_, ?_⟩
  · exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (le_max_left (1 : ℝ) (E / A))
  intro θ hθ
  have hθone : (1 : ℝ) ≤ θ :=
    (le_max_left (1 : ℝ) (E / A)).trans hθ
  have hθnonneg : 0 ≤ θ := le_trans (by norm_num) hθone
  have hdiv : E / A ≤ θ :=
    (le_max_right (1 : ℝ) (E / A)).trans hθ
  have hmul : E ≤ A * θ := by
    have hh : E ≤ θ * A := (div_le_iff₀ hA).mp hdiv
    nlinarith
  have hlow : |D| + |q| + 2 ≤ A * θ - |b| := by
    dsimp [E] at hmul
    linarith
  have hcoef : 0 ≤ A * θ - |b| := by
    have hn : 0 ≤ |D| + |q| + 2 := by positivity
    linarith
  have hscale : A * θ - |b| ≤ (A * θ - |b|) * θ := by
    have hh := mul_le_mul_of_nonneg_left hθone hcoef
    nlinarith
  have hcore : |D| + |q| + 2 ≤ (A * θ - |b|) * θ :=
    hlow.trans hscale
  have hbl : -|b| * θ ≤ b * θ :=
    mul_le_mul_of_nonneg_right (neg_abs_le b) hθnonneg
  have hD : D ≤ |D| := le_abs_self D
  have hq : q ≤ |q| := le_abs_self q
  nlinarith
