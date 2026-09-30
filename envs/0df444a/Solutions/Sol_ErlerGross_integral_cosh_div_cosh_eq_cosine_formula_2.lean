-- Prove2me | solution 2 for ErlerGross.integral_cosh_div_cosh_eq_cosine_formula
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:52:08.665683+00:00
-- url     : https://prove2.me/submissions/800d23e4-cbb9-403d-b2a2-18c0ca3ea75f

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_integral_cosh_div_cosh
open Real Filter Topology MeasureTheory
open ErlerGross

set_option linter.unusedVariables false

theorem solution (a b : Complex)
    (hab : |a.re| < b.re)
    (hI : IntegrableOn (fun x : Real => Complex.cosh (a * x) / Complex.cosh (b * x))
      (Set.Ioi 0)) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0 : Real)))
      (fun x : Real => Complex.cosh (a * x) / Complex.cosh (b * x)) =
      (Real.pi : Complex) / (2 * b) * (1 / Complex.cos (Real.pi * a / (2 * b))) :=
  (integral_cosh_div_cosh a b hab).2
