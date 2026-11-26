-- Prove2me | solution 1 for FriedCrossing.HQuot.taylor2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:08.126489+00:00
-- url     : https://prove2.me/submissions/cf5c2a4c-aad9-452b-8a96-f687fc4f1d09

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_HQuot_slope_eq_strict
import Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ ξ, |ξ| < |τ| ∧ f τ - f 0 - τ * f' 0 = τ ^ 2 * f'' ξ / 2 := by
  set R : ℝ := f τ - f 0 - τ * f' 0 with hR
  -- g(t) := f(t) − f(0) − t·f'(0) − (t²/τ²)·R vanishes at 0 and τ
  set g : ℝ → ℝ := fun t => f t - f 0 - t * f' 0 - t ^ 2 / τ ^ 2 * R with hg
  set g' : ℝ → ℝ := fun t => f' t - f' 0 - 2 * t / τ ^ 2 * R with hg'
  have hgd : ∀ t, HasDerivAt g (g' t) t := fun t => by
    have h1 := ((hf t).sub_const (f 0)).sub ((hasDerivAt_id' t).mul_const (f' 0))
    have h2 := ((hasDerivAt_pow 2 t).div_const (τ ^ 2)).mul_const R
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    simp only [hg']; push_cast; ring
  have hg0 : g 0 = 0 := by simp [hg]
  have hgτ : g τ = 0 := by
    simp only [hg, hR]
    have : τ ^ 2 / τ ^ 2 = 1 := div_self (pow_ne_zero 2 hτ)
    rw [this]; ring
  obtain ⟨ξ₁, hξ₁ne, hξ₁, hslope₁⟩ := slope_eq_strict hgd hτ
  rw [hgτ, hg0, sub_zero, zero_div] at hslope₁
  -- g'(ξ₁) = 0 : f'(ξ₁) − f'(0) = (2ξ₁/τ²)·R
  have hkey : f' ξ₁ - f' 0 = 2 * ξ₁ / τ ^ 2 * R := by
    have := hslope₁.symm; simp only [hg'] at this; linarith
  obtain ⟨ξ, hξ, hslope₂⟩ := Hadamard.entry_slope_eq hf' hξ₁ne
  refine ⟨ξ, lt_trans hξ hξ₁, ?_⟩
  -- (f'(ξ₁) − f'(0))/ξ₁ = f''(ξ) ⇒ f''(ξ) = 2R/τ²
  have h2 : f' ξ₁ - f' 0 = ξ₁ * f'' ξ := by rw [← hslope₂]; field_simp
  have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
  have : ξ₁ * f'' ξ = 2 * ξ₁ / τ ^ 2 * R := by rw [← h2, hkey]
  have h3 : ξ₁ * (f'' ξ * τ ^ 2 - 2 * R) = 0 := by
    have h4 : ξ₁ * f'' ξ * τ ^ 2 = 2 * ξ₁ * R := by
      rw [this]; field_simp
    linear_combination h4
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hξ₁ne
  · linarith
end FriedCrossing.HQuot
