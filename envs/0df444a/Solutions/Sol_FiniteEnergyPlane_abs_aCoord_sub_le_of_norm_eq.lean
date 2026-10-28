-- Prove2me | solution 1 for FiniteEnergyPlane.abs_aCoord_sub_le_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T20:54:03.403247+00:00
-- url     : https://prove2.me/submissions/2cd53b83-da88-4de4-afbe-03f6969f0e55

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- On a circle about `0` inside the punctured unit disc, a smooth function with
`‖z‖ ‖Da(z)‖ ≤ C` is `C`-Lipschitz in the angle. -/
theorem zc_abs_sub_circleMap_le (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a (ball 0 1 \ {0})) {ρ C : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hDa : ∀ z : ℂ, ‖z‖ = ρ → ‖z‖ * ‖fderiv ℝ a z‖ ≤ C) (θ θ' : ℝ) :
    |a (circleMap 0 ρ θ) - a (circleMap 0 ρ θ')| ≤ C * |θ - θ'| := by
  have hU : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hnc : ∀ θ, ‖circleMap 0 ρ θ‖ = ρ := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hρ]
  have hmemU : ∀ θ, circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 \ {0} := by
    intro θ
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, hnc]; exact hρ1
    · intro h; rw [mem_singleton_iff] at h; have := hnc θ; rw [h, norm_zero] at this; linarith
  have hf : ∀ θ ∈ (univ : Set ℝ), HasDerivWithinAt (fun θ => a (circleMap 0 ρ θ))
      (fderiv ℝ a (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) univ θ := by
    intro θ _
    have hfa : HasFDerivAt a (fderiv ℝ a (circleMap 0 ρ θ)) (circleMap 0 ρ θ) :=
      ((ha.contDiffAt (hU.mem_nhds (hmemU θ))).differentiableAt (by simp)).hasFDerivAt
    exact (hfa.comp_hasDerivAt θ (hasDerivAt_circleMap 0 ρ θ)).hasDerivWithinAt
  have hb : ∀ θ ∈ (univ : Set ℝ),
      ‖fderiv ℝ a (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)‖ ≤ C := by
    intro θ _
    refine ((fderiv ℝ a _).le_opNorm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, mul_comm]
    exact hDa _ (hnc θ)
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb (mem_univ θ')
    (mem_univ θ)
  simpa [Real.norm_eq_abs] using this

theorem abs_aCoord_sub_le_of_norm_eq_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (r C : ℝ)
    (hG : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (z z' : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ < r) (hz1 : ‖z‖ < 1) (hzz' : ‖z'‖ = ‖z‖) :
    |aCoord H (u z) - aCoord H (u z')| ≤ 6 * π * C := by
  obtain ⟨-, -, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  have ha : ContDiffOn ℝ ∞ a (ball 0 1 \ {0}) := haCs.comp hu.1 (fun z hz => hu.2.1 z hz)
  set ρ := ‖z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hz
  have hDa : ∀ w : ℂ, ‖w‖ = ρ → ‖w‖ * ‖fderiv ℝ a w‖ ≤ C := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
    refine le_trans ?_ (hG w hw0 (by rw [hw]; exact hzr))
    gcongr
    unfold gradNorm
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hDa z rfl)
  have hzc : circleMap 0 ρ (Complex.arg z) = z := by
    simp [circleMap, hρdef, Complex.norm_mul_exp_arg_mul_I]
  have hzc' : circleMap 0 ρ (Complex.arg z') = z' := by
    rw [show ρ = ‖z'‖ from hzz'.symm]
    simp [circleMap, Complex.norm_mul_exp_arg_mul_I]
  have h := zc_abs_sub_circleMap_le a ha hρ hz1 hDa (Complex.arg z) (Complex.arg z')
  rw [hzc, hzc'] at h
  refine h.trans ?_
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have h3 := Complex.neg_pi_lt_arg z'
  have h4 := Complex.arg_le_pi z'
  have : |Complex.arg z - Complex.arg z'| ≤ 6 * π := by
    rw [abs_le]; constructor <;> linarith [Real.pi_pos]
  calc C * |Complex.arg z - Complex.arg z'| ≤ C * (6 * π) := by gcongr
    _ = 6 * π * C := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (r C : ℝ)
    (hG : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (z z' : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ < r) (hz1 : ‖z‖ < 1) (hzz' : ‖z'‖ = ‖z‖) :
    |aCoord H (u z) - aCoord H (u z')| ≤ 6 * π * C :=
  FiniteEnergyPlane.abs_aCoord_sub_le_of_norm_eq_aux H hH J hJ u hu r C hG z z' hz hzr hz1 hzz'
