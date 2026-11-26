-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrderInLastVariable_iff_analyticOrderAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:58.758802+00:00
-- url     : https://prove2.me/submissions/cd21dc65-204d-484f-bdc8-212469954c28

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Theorems.Thm_ClassicalComplexWPT_analyticAt_lastSlice
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ExactOrderInLastVariable f d ↔ analyticOrderAt (lastSlice f) 0 = d := by
  simpa [ExactOrderInLastVariable] using
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticAt_lastSlice hf) (n := d)).symm
end ClassicalComplexWPT
