-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/63a40873-ab18-45bc-800f-7d1d25888870

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_factorized
import Theorems.Thm_CohnElkies_gamma_log_coth_ratio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) := by
  calc
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) :=
      lowerGammaBoundaryLog_halfInteger_factorized k R hy
    _ = ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) := by
      congr 1
      simpa [abs_div, mul_div_assoc] using!
        (gamma_log_coth_ratio
          (x := y / 2) (div_ne_zero hy (by norm_num)))
end CohnElkies
