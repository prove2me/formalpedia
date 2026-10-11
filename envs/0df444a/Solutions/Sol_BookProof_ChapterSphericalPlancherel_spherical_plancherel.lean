-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.spherical_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:02.554812+00:00
-- url     : https://prove2.me/submissions/48569f02-3ddf-4c7a-987c-7edd272950eb

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.spherical_plancherel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_sineKernel_plancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_sphericalTransform_eq
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x)
    (f : ℝ → ℂ) (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) :
    ∫ p in Ioi (0 : ℝ), ‖sphericalTransform f p‖ ^ 2 * p ^ 2
      = ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * r ^ 2 := by

  have hpi : (0 : ℝ) < π := Real.pi_pos
  -- the right-hand side is the `L²(dr)` norm of `G`
  have hR : ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * r ^ 2 = ∫ r in Ioi (0 : ℝ), ‖G r‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have : ‖G r‖ = ‖(r : ℂ) * f r‖ := by rw [hf r hr]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  -- the left-hand side is `(2/π)` times the sine-transform energy
  have hL : ∫ p in Ioi (0 : ℝ), ‖sphericalTransform f p‖ ^ 2 * p ^ 2
      = (2 / π) * ∫ p in Ioi (0 : ℝ), ‖sineKernelTransform (⇑G) p‖ ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun p hp => ?_
    have hp0 : (0 : ℝ) < p := hp
    have hval : ‖sphericalTransform f p‖
        = Real.sqrt (2 / π) * (p⁻¹ * ‖sineKernelTransform (⇑G) p‖) := by
      rw [sphericalTransform_eq hf hp0, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    rw [hval, mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 / π), inv_pow]
    field_simp
  rw [hL, hR, sineKernel_plancherel G hodd]
  field_simp
