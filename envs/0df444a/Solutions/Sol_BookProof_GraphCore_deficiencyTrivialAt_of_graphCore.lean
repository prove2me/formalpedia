-- Prove2me | solution 1 for BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:49:02.604996+00:00
-- url     : https://prove2.me/submissions/6fcf0fd9-b1e3-43f5-9853-bea0fd3fac07

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) {z : ℂ}
    (h₂ : DeficiencyTrivialAt D₂ T z) :
    DeficiencyTrivialAt D₁ (restrictOp T h) z := by

  intro w hw
  refine h₂ w ?_
  intro v
  -- the defect of `v`, which we show to be arbitrarily small
  set c : ℂ := (inner ℂ (T v) w : ℂ) - z * inner ℂ (v : F) w with hc
  have hsmall : ∀ ε > 0, ‖c‖ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
    intro ε hε
    obtain ⟨y, hyD₁, hy₁, hy₂⟩ := hcore v ε hε
    have hy : (inner ℂ (T y) w : ℂ) = z * inner ℂ (y : F) w := by
      have hre : restrictOp T h ⟨(y : F), hyD₁⟩ = T y := rfl
      have := hw ⟨(y : F), hyD₁⟩
      rw [hre] at this
      exact this
    have hcc : c = (inner ℂ (T v - T y) w : ℂ) - z * inner ℂ ((v : F) - (y : F)) w := by
      rw [hc, inner_sub_left, inner_sub_left, hy]; ring
    have h1 : ‖(inner ℂ (T v - T y) w : ℂ)‖ ≤ ε * ‖w‖ := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_right hy₂.le (norm_nonneg w)
    have h2 : ‖z * (inner ℂ ((v : F) - (y : F)) w : ℂ)‖ ≤ ‖z‖ * (ε * ‖w‖) := by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg z)
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_right hy₁.le (norm_nonneg w)
    calc ‖c‖ ≤ ‖(inner ℂ (T v - T y) w : ℂ)‖ + ‖z * (inner ℂ ((v : F) - (y : F)) w : ℂ)‖ := by
          rw [hcc]; exact norm_sub_le _ _
      _ ≤ ε * ‖w‖ + ‖z‖ * (ε * ‖w‖) := add_le_add h1 h2
      _ = ε * (1 + ‖z‖) * ‖w‖ := by ring
  have : c = 0 := by
    by_contra hne
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
    set M : ℝ := (1 + ‖z‖) * ‖w‖ with hM
    have hMpos : 0 < M := by
      rcases lt_or_eq_of_le (norm_nonneg w) with hw0 | hw0
      · have : 0 < 1 + ‖z‖ := by positivity
        exact mul_pos this hw0
      · exfalso
        have hw' : w = 0 := by
          have : ‖w‖ = 0 := hw0.symm
          exact norm_eq_zero.mp this
        have : c = 0 := by simp [hc, hw']
        exact hne this
    obtain ⟨ε, hε, hεlt⟩ : ∃ ε > 0, ε * M < ‖c‖ :=
      ⟨‖c‖ / (2 * M), by positivity, by
        have hM0 : M ≠ 0 := ne_of_gt hMpos
        have h2 : ‖c‖ / (2 * M) * M = ‖c‖ / 2 := by field_simp
        rw [h2]; linarith⟩
    have := hsmall ε hε
    rw [mul_assoc] at this
    linarith
  rw [hc] at this
  exact sub_eq_zero.mp this
