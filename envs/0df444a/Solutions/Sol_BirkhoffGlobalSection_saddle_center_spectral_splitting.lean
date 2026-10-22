-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_spectral_splitting
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:56:24.305949+00:00
-- url     : https://prove2.me/submissions/1c3d5cb7-0f0b-4efb-b81b-7f34da1c32c2

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

theorem aux_scss_formula (v : Phase) :
    TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec v)) =
      ![-v 1 + v 2, v 0 + v 3, 16 * v 0 - v 3, -8 * v 1 + v 2] := by
  funext i
  fin_cases i <;>
    simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution :
    ∃ ω lam : ℝ, 0 < ω ∧ 0 < lam ∧ ∃ e₁ e₂ f₁ f₂ : Phase,
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₁)) = ω • e₂ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₂)) = -ω • e₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₁)) = lam • f₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₂)) = -lam • f₂ ∧
      LinearIndependent ℝ ![e₁, e₂, f₁, f₂] := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = 2 :=
    ⟨Real.sqrt 2, by positivity, Real.sq_sqrt (by norm_num)⟩
  have hs1 : 1 < s := by nlinarith
  obtain ⟨ω, hω0, hω⟩ : ∃ ω : ℝ, 0 < ω ∧ ω ^ 2 = 8 * s - 3 :=
    ⟨Real.sqrt (8 * s - 3), Real.sqrt_pos.mpr (by linarith),
      Real.sq_sqrt (by linarith)⟩
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 < L ∧ L ^ 2 = 3 + 8 * s :=
    ⟨Real.sqrt (3 + 8 * s), Real.sqrt_pos.mpr (by linarith),
      Real.sq_sqrt (by linarith)⟩
  refine ⟨ω, L, hω0, hL0, ![5 - 4 * s, 0, 0, -2 - 4 * s],
    ![0, -ω, -ω * (6 - 4 * s), 0],
    ![5 + 4 * s, L, L * (6 + 4 * s), 4 * s - 2],
    ![5 + 4 * s, -L, -L * (6 + 4 * s), 4 * s - 2], ?_, ?_, ?_, ?_, ?_⟩
  · rw [aux_scss_formula]
    funext i
    fin_cases i <;> simp
    · linear_combination hω
    · linear_combination (6 - 4 * s) * hω - 32 * hs
  · rw [aux_scss_formula]
    funext i
    fin_cases i <;> simp <;> ring
  · rw [aux_scss_formula]
    funext i
    fin_cases i <;> simp <;>
      first
      | ring1
      | linear_combination hL
      | linear_combination (-1 : ℝ) * hL
      | linear_combination (6 + 4 * s) * hL + 32 * hs
      | linear_combination (-(6 + 4 * s)) * hL - 32 * hs
  · rw [aux_scss_formula]
    funext i
    fin_cases i <;> simp <;>
      first
      | ring1
      | linear_combination hL
      | linear_combination (-1 : ℝ) * hL
      | linear_combination (6 + 4 * s) * hL + 32 * hs
      | linear_combination (-(6 + 4 * s)) * hL - 32 * hs
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    have h2 := congrFun hg 2
    have h3 := congrFun hg 3
    simp [Fin.sum_univ_four] at h0 h1 h2 h3
    have k0 : g 0 * (56 * s) = 0 := by
      linear_combination (4 * s - 2) * h0 - (5 + 4 * s) * h3
    have g0 : g 0 = 0 := by
      rcases mul_eq_zero.mp k0 with h | h
      · exact h
      · exact absurd h (by positivity)
    have k1 : (g 2 + g 3) * (5 + 4 * s) = 0 := by
      rw [g0] at h0; linear_combination h0
    have g23 : g 2 + g 3 = 0 := by
      rcases mul_eq_zero.mp k1 with h | h
      · exact h
      · exact absurd h (by positivity)
    have k2 : (g 2 - g 3) * (L * (8 * s)) = 0 := by
      linear_combination h2 - (6 - 4 * s) * h1
    have g2m3 : g 2 - g 3 = 0 := by
      rcases mul_eq_zero.mp k2 with h | h
      · exact h
      · exact absurd h (by positivity)
    have g2 : g 2 = 0 := by linarith
    have g3 : g 3 = 0 := by linarith
    have k3 : g 1 * ω = 0 := by
      rw [g2, g3] at h1; linear_combination -h1
    have g1 : g 1 = 0 := by
      rcases mul_eq_zero.mp k3 with h | h
      · exact h
      · exact absurd h (by positivity)
    intro i
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
    · exact g3
