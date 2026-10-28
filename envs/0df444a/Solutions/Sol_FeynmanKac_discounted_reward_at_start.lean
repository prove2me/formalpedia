-- Prove2me | solution 1 for FeynmanKac.discounted_reward_at_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:02:29.111562+00:00
-- url     : https://prove2.me/submissions/0d3cf5b1-5136-4ff9-bb70-f18d04f6920f

import Definitions.Def_FeynmanKac_PathDiscount
import Definitions.Def_FeynmanKac_DiscountedReward
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The discounted Feynman–Kac reward starts at the value of the
candidate PDE solution because the initial discount is one and the
running-payment integral over a degenerate interval is zero. -/
theorem solution
    {Ω : Type*} (X : ℝ → Ω → ℝ)
    (V u f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) :
    FeynmanKac.discountedReward X V u f t t ω = u (X t ω) t := by
  simp [FeynmanKac.discountedReward, FeynmanKac.pathDiscount]
