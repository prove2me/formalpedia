-- Prove2me | solution 1 for FiniteEnergyPlane.integral_norm_sq_le_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T00:27:24.978918+00:00
-- url     : https://prove2.me/submissions/c78c10b4-93b0-43a9-a489-d8ce0b8ac4f0

import Mathlib

open scoped RealInnerProductSpace
open MeasureTheory Set

/-! A Poincaré inequality on an interval for a curve vanishing at the left endpoint, with the
derivative twisted by a skew operator. -/


namespace FiniteEnergyPlane

theorem integral_norm_sq_le_of_skew_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : ∀ v, ⟪v, T v⟫ = 0) (w w' : ℝ → E)
    (hw : ∀ t, HasDerivAt w (w' t) t) (hw' : Continuous w') (x₀ L : ℝ) (hL : 0 < L)
    (h0 : w x₀ = 0) :
    ∫ t in x₀..x₀ + L, ‖w t‖ ^ 2 ≤ 4 * L ^ 2 * ∫ t in x₀..x₀ + L, ‖w' t - T (w t)‖ ^ 2 := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  set h : ℝ → E := fun t => w' t - T (w t)
  have hhc : Continuous h := hw'.sub (T.continuous.comp hwc)
  have hφ : ∀ t, HasDerivAt (fun t => ‖w t‖ ^ 2) (2 * ⟪w t, h t⟫) t := by
    intro t
    refine ((hw t).norm_sq).congr_deriv ?_
    simp only [h, inner_sub_right, hT, sub_zero]
  set ψ : ℝ → ℝ := fun t => ‖w t‖ ^ 2 / (2 * L) + 2 * L * ‖h t‖ ^ 2
  have hψc : Continuous ψ := ((hwc.norm.pow 2).div_const _).add (continuous_const.mul (hhc.norm.pow 2))
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => by positivity
  have hpt : ∀ t, 2 * ⟪w t, h t⟫ ≤ ψ t := by
    intro t
    have h1 := real_inner_le_norm (w t) (h t)
    have h2 : 2 * (‖w t‖ * ‖h t‖) ≤ ψ t := by
      simp only [ψ]
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖w t‖ - 2 * L * ‖h t‖)]
    linarith
  set P := ∫ t in x₀..x₀ + L, ψ t
  have hbd : ∀ t ∈ Icc x₀ (x₀ + L), ‖w t‖ ^ 2 ≤ P := by
    intro t ht
    have hfun : ∫ s in x₀..t, 2 * ⟪w s, h s⟫ = ‖w t‖ ^ 2 - ‖w x₀‖ ^ 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ s)
        ((continuous_const.mul (hwc.inner hhc)).intervalIntegrable _ _)
    rw [h0, norm_zero] at hfun
    have h1 : ∫ s in x₀..t, 2 * ⟪w s, h s⟫ ≤ ∫ s in x₀..t, ψ s :=
      intervalIntegral.integral_mono_on ht.1
        ((continuous_const.mul (hwc.inner hhc)).intervalIntegrable _ _)
        (hψc.intervalIntegrable _ _) fun s _ => hpt s
    have h2 : ∫ s in x₀..t, ψ s ≤ P :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall hψ0) (hψc.intervalIntegrable _ _)
    have : (0:ℝ) ^ 2 = 0 := by norm_num
    linarith
  have hX : ∫ t in x₀..x₀ + L, ‖w t‖ ^ 2 ≤ ∫ t in x₀..x₀ + L, P :=
    intervalIntegral.integral_mono_on (by linarith) ((hwc.norm.pow 2).intervalIntegrable _ _)
      intervalIntegrable_const fun t ht => hbd t ht
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hX
  have hP : P = (∫ t in x₀..x₀ + L, ‖w t‖ ^ 2) / (2 * L) +
      2 * L * ∫ t in x₀..x₀ + L, ‖h t‖ ^ 2 := by
    simp only [P, ψ]
    rw [intervalIntegral.integral_add (f := fun t => ‖w t‖ ^ 2 / (2 * L))
      (g := fun t => 2 * L * ‖h t‖ ^ 2)
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  rw [hP] at hX
  have e : L * ((∫ t in x₀..x₀ + L, ‖w t‖ ^ 2) / (2 * L)) = (∫ t in x₀..x₀ + L, ‖w t‖ ^ 2) / 2 := by
    field_simp
  rw [mul_add, e] at hX
  simp only [h] at hX ⊢
  nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory
open scoped RealInnerProductSpace

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : ∀ v, ⟪v, T v⟫ = 0) (w w' : ℝ → E)
    (hw : ∀ t, HasDerivAt w (w' t) t) (hw' : Continuous w') (x₀ L : ℝ) (hL : 0 < L)
    (h0 : w x₀ = 0) :
    ∫ t in x₀..x₀ + L, ‖w t‖ ^ 2 ≤ 4 * L ^ 2 * ∫ t in x₀..x₀ + L, ‖w' t - T (w t)‖ ^ 2 :=
  integral_norm_sq_le_of_skew_aux T hT w w' hw hw' x₀ L hL h0
