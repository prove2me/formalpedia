-- Prove2me | solution 1 for FairSelling.reduction_budget
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:23:51.37892+00:00
-- url     : https://prove2.me/submissions/1f79227d-f67c-4480-a7cd-bfaaed85fc08

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction
set_option autoImplicit true
open FairSelling


theorem solution (μ : ℝ) (hμ : 0 ≤ μ) (n0 n2 n4 t : ℕ) (ht : t ≤ n2) (Gval : ℝ)
    (hG : ((n0 : ℝ) + n2 + n4) * μ - (n2 : ℝ) * ((2 / 3) * μ) - (n4 : ℝ) * μ
        - 2 * (t : ℝ) * ((2 / 3) * μ) ≤ Gval) :
    ((n0 : ℝ) - t) * μ ≤ Gval := by
  have ht' : (t:ℝ) ≤ n2 := by exact_mod_cast ht
  nlinarith [mul_nonneg (sub_nonneg.mpr ht') hμ]
