-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_source_faithful_cash_bound_with_prepayment_defect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:06:01.872627+00:00
-- url     : https://prove2.me/submissions/a6d00de9-a699-424d-abfb-4118a975064d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
open MeasureTheory AvramDividend.Classical
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {ι : Type*} (s : Finset ι)
    (E : ι → ℝ) (pre post : ι → ℝ) (w V : ℝ → ℝ)
    (initial final Cash eps : ℝ)
    (hInit : V initial = w initial)
    (hFinal : V final = w final)
    (hPost : ∀ i ∈ s, V (post i) = w (post i))
    (hCaplinear : Cash + (V initial - V final) -
        (∑ i ∈ s, E i * (V (pre i) - V (post i))) ≤ eps) :
    Cash + (w initial - w final) +
        (∑ i ∈ s, E i * (w (post i) - w (pre i))) ≤
      eps + (∑ i ∈ s, E i * (V (pre i) - w (pre i))) := by
  have hEq :=
    avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
      s E pre post w V initial final hInit hFinal hPost
  linarith only [hCaplinear, hEq]