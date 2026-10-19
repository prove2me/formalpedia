-- Prove2me | solution 1 for CohnElkies.exp_integral_upperCenteredLaplaceKernel_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/d81b565a-b7f9-4776-97ec-42bd937a61bb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exp_integral_upperCenteredLaplaceKernel

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
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      (((s * c : ℝ) : ℂ) /
          (((s * c : ℝ) : ℂ) -
            Complex.I * ((s * T : ℝ) : ℂ))) *
        Complex.exp
          (-Complex.I *
            (((s * T / (s * c) : ℝ) : ℂ))) := by
  have hcn : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hsn : (s : ℂ) ≠ 0 := by
    exact_mod_cast hs.ne'
  have hzn : (c : ℂ) - Complex.I * (T : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using! hc.ne'
  have hratio :
      (c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ)) =
        (((s * c : ℝ) : ℂ) /
          (((s * c : ℝ) : ℂ) -
            Complex.I * ((s * T : ℝ) : ℂ))) := by
    push_cast
    field_simp [hcn, hsn, hzn]
  have hphase : T / c = s * T / (s * c) := by
    field_simp [hc.ne', hs.ne']
  rw [exp_integral_upperCenteredLaplaceKernel hc T,
    hratio, hphase]
end CohnElkies
