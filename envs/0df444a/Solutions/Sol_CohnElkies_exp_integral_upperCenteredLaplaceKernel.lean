-- Prove2me | solution 1 for CohnElkies.exp_integral_upperCenteredLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/8eb28aed-d0b9-44c8-b803-3c1288ff833a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_upperCenteredLaplaceKernel

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      ((c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ))) *
        Complex.exp
          (-Complex.I * ((T / c : ℝ) : ℂ)) := by
  have hcn : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hzn : (c : ℂ) - Complex.I * (T : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using! hc.ne'
  have hphase :
      -(Complex.I * (T : ℂ) * (c : ℂ)⁻¹) =
        -Complex.I * ((T / c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [integral_upperCenteredLaplaceKernel hc T]
  calc
    Complex.exp
        (Complex.log (c : ℂ) -
          Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹) =
        Complex.exp
          (Complex.log (c : ℂ) -
            Complex.log ((c : ℂ) - Complex.I * (T : ℂ))) *
          Complex.exp
            (-Complex.I * ((T / c : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [← hphase]
      ring
    _ = ((c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ))) *
        Complex.exp
          (-Complex.I * ((T / c : ℝ) : ℂ)) := by
      rw [Complex.exp_sub,
        Complex.exp_log hcn, Complex.exp_log hzn]
end CohnElkies
