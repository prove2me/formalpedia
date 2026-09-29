-- Prove2me | solution 1 for Freiman.constant_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T02:22:44.665387+00:00
-- url     : https://prove2.me/submissions/3456eae7-16ee-4248-a8fe-09f096b1cce0

import Definitions.Def_Freiman_cF
import Definitions.Def_Freiman_gapThreshold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

private theorem sqrt_bounds (x l u : ℝ) (hx : 0 ≤ x) (hl : 0 ≤ l)
    (hlo : l ^ 2 < x) (hu : x < u ^ 2) (hup : 0 ≤ u) :
    l < Real.sqrt x ∧ Real.sqrt x < u := by
  have hsq := Real.sq_sqrt hx
  have hp := Real.sqrt_nonneg x
  constructor <;> nlinarith

open Freiman in
theorem solution :
    gapLeft < gapThreshold ∧ gapThreshold < cF ∧
    cF < Real.sqrt 21 ∧ Real.sqrt 21 < upperRayStart ∧
    upperRayStart < (128 / 25 : ℝ) := by
  obtain ⟨h21l, h21u⟩ := sqrt_bounds 21 (4582575 / 1000000) (4582576 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h462l, h462u⟩ := sqrt_bounds 462 (21494185 / 1000000) (21494186 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h243542l, h243542u⟩ := sqrt_bounds 243542 (493499746 / 1000000)
    (493499747 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold gapLeft gapThreshold cF upperRayStart
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
