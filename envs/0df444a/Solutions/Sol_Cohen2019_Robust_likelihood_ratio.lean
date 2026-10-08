-- Prove2me | solution 1 for Cohen2019.Robust.likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:18:09.266669+00:00
-- url     : https://prove2.me/submissions/92188c5f-9d22-42d6-870a-753d059e5608

import Mathlib
import Definitions.Def_Cohen2019_Robust_gaussDens

open MeasureTheory ProbabilityTheory Cohen2019.Robust in
theorem bf3da223_ratio {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) : gaussDens (x + δ) σ z
      = Real.exp (1 / σ ^ 2 * inner ℝ δ z + -(2 * inner ℝ δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))
        * gaussDens x σ z := by
  unfold gaussDens
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  have h1 : z - (x + δ) = (z - x) - δ := by abel
  rw [h1, norm_sub_sq_real, inner_sub_left, real_inner_comm z δ, real_inner_comm x δ]
  have hs : σ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

open MeasureTheory ProbabilityTheory Cohen2019.Robust in
theorem bf3da223_pos {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x z : EuclideanSpace ℝ (Fin d)) :
    0 < gaussDens x σ z := by
  unfold gaussDens
  have : 0 < 2 * Real.pi * σ ^ 2 := by positivity
  exact mul_pos (Real.rpow_pos_of_pos this _) (Real.exp_pos _)

open MeasureTheory ProbabilityTheory Cohen2019.Robust in
theorem solution {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) :
    (∀ z, gaussDens (x + δ) σ z
      = Real.exp (1 / σ ^ 2 * inner ℝ δ z + -(2 * inner ℝ δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))
        * gaussDens x σ z) ∧
    (∀ β : ℝ, ∃ t : ℝ, 0 < t ∧
      {z | inner ℝ δ z ≤ β} = {z | gaussDens (x + δ) σ z ≤ t * gaussDens x σ z} ∧
      {z | β ≤ inner ℝ δ z} = {z | t * gaussDens x σ z ≤ gaussDens (x + δ) σ z}) := by
  have hr := bf3da223_ratio σ hσ x δ
  refine ⟨hr, fun β => ?_⟩
  have ha : 0 < 1 / σ ^ 2 := by positivity
  refine ⟨Real.exp (1 / σ ^ 2 * β + -(2 * inner ℝ δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)),
    Real.exp_pos _, ?_, ?_⟩
  · ext z
    simp only [Set.mem_setOf_eq]
    rw [hr z, mul_le_mul_iff_left₀ (bf3da223_pos σ hσ x z), Real.exp_le_exp,
      add_le_add_iff_right]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h ha.le
    · intro h; exact le_of_mul_le_mul_left h ha
  · ext z
    simp only [Set.mem_setOf_eq]
    rw [hr z, mul_le_mul_iff_left₀ (bf3da223_pos σ hσ x z), Real.exp_le_exp,
      add_le_add_iff_right]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h ha.le
    · intro h; exact le_of_mul_le_mul_left h ha
