-- Prove2me | solution 1 for BookProof.RadialMollifier.integral_moll_eq_self_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:23.412616+00:00
-- url     : https://prove2.me/submissions/02eb7228-22b7-4d89-9563-2c1d0b708272

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.integral_moll_eq_self_of_analytic
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_moll_eq_zero_of_le
import Theorems.Thm_BookProof_RadialMollifier_moll_integral
import Theorems.Thm_BookProof_RadialMollifier_polar_radial
import Theorems.Thm_BookProof_RadialMollifier_circle_integral_eq
import Theorems.Thm_BookProof_RadialMollifier_polarSymm_eq
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : closedBall z δ ⊆ s) :
    ∫ w : ℂ, (moll δ (z - w) : ℂ) * h w = h z := by

  have hswap : (∫ w : ℂ, (moll δ (z - w) : ℂ) * h w)
      = ∫ u : ℂ, (moll δ u : ℂ) * h (z - u) := by
    have := integral_sub_left_eq_self (fun u : ℂ => (moll δ u : ℂ) * h (z - u)) volume z
    simpa using this
  set A : ℂ := ∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ) : ℂ) with hA
  -- normalization: A * 2π = 1
  have hnorm : A * ((2 * π : ℝ) : ℂ) = 1 := by
    have h1 := polar_radial hδ (fun _ => (1 : ℂ)) continuous_const
    have hL : (∫ u : ℂ, (moll δ u : ℂ) * 1) = 1 := by
      simp only [mul_one]
      rw [integral_complex_ofReal, moll_integral hδ]
      norm_num
    have hR : (∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ) : ℂ) *
        ∫ _θ in (-π)..π, (1 : ℂ)) = A * ((2 * π : ℝ) : ℂ) := by
      rw [hA, ← MeasureTheory.integral_mul_const]
      congr 1
      funext r
      congr 1
      rw [intervalIntegral.integral_const]
      simp [Complex.real_smul]
      ring
    rw [hL, hR] at h1
    exact h1.symm
  -- the main polar computation
  have h2 := polar_radial hδ (fun u => h (z - u)) (hcont.comp (continuous_const.sub continuous_id))
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      ((r * moll δ r : ℝ) : ℂ) * (∫ θ in (-π)..π, h (z - Complex.polarCoord.symm (r, θ)))
        = ((r * moll δ r : ℝ) : ℂ) * (((2 * π : ℝ) : ℂ) * h z) := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hrd : r < δ
    · congr 1
      simp only [polarSymm_eq]
      exact circle_integral_eq hs hh hr0
        ((closedBall_subset_closedBall hrd.le).trans hz)
    · have : moll δ (r : ℂ) = 0 := by
        refine moll_eq_zero_of_le hδ ?_
        simpa [abs_of_pos hr0] using not_lt.1 hrd
      simp [this]
  rw [hswap, h2, setIntegral_congr_fun measurableSet_Ioi hpt]
  simp only [← mul_assoc]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, ← hA, hnorm, one_mul]
