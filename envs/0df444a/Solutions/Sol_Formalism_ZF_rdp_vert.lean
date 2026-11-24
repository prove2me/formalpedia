-- Prove2me | solution 1 for Formalism.ZF.rdp_vert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:06.438798+00:00
-- url     : https://prove2.me/submissions/9a465b02-92e8-4082-b83e-eb108b3257d8

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Theorems.Thm_Formalism_ZF_rdp_hasDerivAt_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (a p : ℂ) (x y0 y1 : ℝ) (hx : x ≠ p.re) :
    I * ∫ y in y0..y1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x : ℂ) + y1 * I - p)⁻¹) - (-a * ((x : ℂ) + y0 * I - p)⁻¹) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I ≠ p := by
    intro y h
    apply hx
    have := congrArg Complex.re h
    simpa using this
  have hder : ∀ y : ℝ, HasDerivAt (fun t : ℝ => -a * ((x : ℂ) + t * I - p)⁻¹)
      (I * (a / ((x : ℂ) + y * I - p) ^ 2)) y := by
    intro y
    have hh : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne y)).comp y hh
    simp only [Function.comp_def] at h2
    exact h2.congr_deriv (mul_comm _ _)
  have hcont : Continuous (fun y : ℝ => I * (a / ((x : ℂ) + y * I - p) ^ 2)) := by
    refine continuous_const.mul (Continuous.div continuous_const (by fun_prop) (fun y => ?_))
    exact pow_ne_zero _ (sub_ne_zero.2 (hne y))
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
    (hcont.intervalIntegrable _ _)
end Formalism.ZF
