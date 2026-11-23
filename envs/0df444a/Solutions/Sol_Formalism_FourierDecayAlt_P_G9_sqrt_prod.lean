-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.sqrt_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:11.233402+00:00
-- url     : https://prove2.me/submissions/b7e3050e-736d-42f6-ba7b-600f2bbd5b0f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (δ r : ℝ) (hδ : 0 < δ) :
    ((Real.pi : ℂ) / ((δ : ℂ) - r * Complex.I)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / ((δ : ℂ) + r * Complex.I)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  set b : ℂ := (δ : ℂ) - r * Complex.I with hb
  have hcb : (starRingEnd ℂ) b = (δ : ℂ) + r * Complex.I := by
    simp [hb]
  have hbre : b.re = δ := by simp [hb]
  have hbim : b.im = -r := by simp [hb]
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hbre; simp at hbre; linarith
  set z : ℂ := (Real.pi : ℂ) / b with hz
  have hcz : (starRingEnd ℂ) z = (Real.pi : ℂ) / ((δ : ℂ) + r * Complex.I) := by
    rw [hz, map_div₀, hcb, Complex.conj_ofReal]
  have hzre : 0 < z.re := by
    rw [hz, Complex.div_re]
    have : 0 < Complex.normSq b := Complex.normSq_pos.2 hb0
    simp only [Complex.ofReal_re, Complex.ofReal_im, hbre, zero_mul, zero_div, add_zero]
    have := Real.pi_pos
    positivity
  have harg : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  rw [← hcz, Complex.conj_cpow z _ harg]
  have h12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.conj_ofReal]
  rw [h12, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ‖z ^ (1 / 2 : ℂ)‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
    have := Complex.norm_cpow_real z (1 / 2 : ℝ)
    rw [← this]; congr 2; push_cast; ring
  rw [h3, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _)]
  congr 1
  rw [hz, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply, hbre, hbim]
  congr 1; ring
end Formalism.FourierDecayAlt.P.G9
