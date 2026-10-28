-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_product_integrable_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:09:44.928591+00:00
-- url     : https://prove2.me/submissions/3200d034-3363-4d6a-8b0b-3636966bcc8c

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The product in any full causal convolution has compact support. -/
theorem solution
    (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfzero : ∀ y : ℝ, y < 0 → f y = 0)
    (hgzero : ∀ y : ℝ, y < 0 → g y = 0) :
    ∀ x : ℝ,
      Integrable (fun y : ℝ => f y * g (x - y)) volume := by
  intro x
  have hcont : Continuous (fun y : ℝ => f y * g (x - y)) :=
    hf.mul (hg.comp (continuous_const.sub continuous_id))
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    (K := Icc (0 : ℝ) (max 0 x)) isCompact_Icc
  intro y hy
  by_cases hneg : y < 0
  · simp [hfzero y hneg]
  · have h0y : 0 ≤ y := le_of_not_gt hneg
    have hxy : x < y := by
      by_contra hnot
      have hyx : y ≤ x := le_of_not_gt hnot
      exact hy ⟨h0y, le_trans hyx (le_max_right 0 x)⟩
    have hdiff : x - y < 0 := sub_neg.mpr hxy
    simp [hgzero (x - y) hdiff]
