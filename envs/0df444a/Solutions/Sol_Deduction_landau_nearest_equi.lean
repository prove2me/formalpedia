-- Prove2me | solution 1 for Deduction.landau_nearest_equi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:19.654718+00:00
-- url     : https://prove2.me/submissions/d9f1204a-403b-402f-9758-3c0e5545bac7

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauFinite
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauNearest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {σ γ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (h : ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖)
    (hγ : γ ≠ ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) / (2 * (a.im - b.im))) :
    a = b := by
  have h2 : ‖(σ : ℂ) + γ * I - a‖ ^ 2 = ‖(σ : ℂ) + γ * I - b‖ ^ 2 := by rw [h]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
  have him : a.im = b.im := by
    by_contra hne
    apply hγ
    have hne' : 2 * (a.im - b.im) ≠ 0 := by
      have := sub_ne_zero.mpr hne
      positivity
    rw [eq_div_iff hne']
    linear_combination -h2
  have hsq : (b.re - a.re) * ((σ - a.re) + (σ - b.re)) = 0 := by
    rw [him] at h2
    linear_combination h2
  rcases mul_eq_zero.mp hsq with h3 | h3
  · apply Complex.ext
    · linarith
    · exact him
  · exfalso
    linarith
end Deduction
