-- Prove2me | solution 1 for DynamicsRelativity.conic_ecc_lt_one_isEllipse
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T05:05:34.47456+00:00
-- url     : https://prove2.me/submissions/a51ef32a-9d43-4d39-9d43-59c5e65565e9

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem solution {n A : Vec} {r₀ : ℝ}
    (hn : n ≠ 0) (hnA : inner ℝ n A = 0) (hr₀ : 0 < r₀) (hA : ‖A‖ < 1) :
    IsEllipseWithFocusAtOrigin {y : Vec | inner ℝ n y = 0 ∧ ‖y‖ + inner ℝ A y = r₀} := by
  set e := ‖A‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have h1e : 0 < 1 - e ^ 2 := by nlinarith
  set a := r₀ / (1 - e ^ 2) with hadef
  have ha : 0 < a := div_pos hr₀ h1e
  have hae : a * (1 - e ^ 2) = r₀ := by rw [hadef]; field_simp
  -- expansion of the distance to the second focus `c = -(2a) A`
  have hexp : ∀ y : Vec, ‖y - -(2 * a) • A‖ ^ 2 = ‖y‖ ^ 2 + 4 * a * inner ℝ A y + 4 * a ^ 2 * e ^ 2 := by
    intro y
    rw [neg_smul, sub_neg_eq_add, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * a), real_inner_comm]
    ring
  refine ⟨n, -(2 * a) • A, a, hn, ?_, ?_, ?_⟩
  · rw [inner_smul_right, hnA, mul_zero]
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
    nlinarith
  · ext y
    simp only [Set.mem_setOf_eq]
    have hcs : |inner ℝ A y| ≤ e * ‖y‖ := abs_real_inner_le_norm A y
    have hcs' := abs_le.mp hcs
    have hy0 := norm_nonneg y
    constructor
    · rintro ⟨hy, hy2⟩
      refine ⟨hy, ?_⟩
      -- 2a - ‖y‖ ≥ 0
      have hr : ‖y‖ * (1 - e) ≤ r₀ := by nlinarith
      have hnn : 0 ≤ 2 * a - ‖y‖ := by
        have h2 : ‖y‖ * (1 - e ^ 2) ≤ 2 * r₀ := by nlinarith
        have : ‖y‖ * (1 - e ^ 2) ≤ 2 * a * (1 - e ^ 2) := by nlinarith
        nlinarith
      have hsq : ‖y - -(2 * a) • A‖ ^ 2 = (2 * a - ‖y‖) ^ 2 := by
        rw [hexp]
        have hs : inner ℝ A y = r₀ - ‖y‖ := by linarith
        rw [hs, ← hae]
        ring
      have := (sq_eq_sq₀ (norm_nonneg _) hnn).mp hsq
      linarith
    · rintro ⟨hy, hy2⟩
      refine ⟨hy, ?_⟩
      have hnn : 0 ≤ 2 * a - ‖y‖ := by linarith [norm_nonneg (y - -(2 * a) • A)]
      have hsq : ‖y - -(2 * a) • A‖ ^ 2 = (2 * a - ‖y‖) ^ 2 := by
        rw [show ‖y - -(2 * a) • A‖ = 2 * a - ‖y‖ by linarith]
      rw [hexp] at hsq
      -- 4a(a(1-e²) - ‖y‖ - ⟨A,y⟩) = 0
      have h4 : 4 * a * (a * (1 - e ^ 2) - ‖y‖ - inner ℝ A y) = 0 := by nlinarith
      have : a * (1 - e ^ 2) - ‖y‖ - inner ℝ A y = 0 := by
        rcases mul_eq_zero.mp h4 with h | h
        · exact absurd h (by positivity)
        · exact h
      linarith
