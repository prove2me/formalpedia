-- Prove2me | solution 1 for AvramDividend.Classical.avram_a126_real_factorial_void_squeeze_limit_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:45:46.430858+00:00
-- url     : https://prove2.me/submissions/bdf93846-8b58-414b-a67c-9014f058083b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (q : ℕ → ℝ) (rate : ℝ)
    (hLower : ∀ᶠ n : ℕ in Filter.atTop,
      rate - rate ^ 2 / (n : ℝ) ≤ q n)
    (hUpper : ∀ᶠ n : ℕ in Filter.atTop, q n ≤ rate) :
    Filter.Tendsto q Filter.atTop (nhds rate) := by
  have hLimit : Filter.Tendsto
      (fun n : ℕ => rate - rate ^ 2 / (n : ℝ))
      Filter.atTop (nhds rate) := by
    simpa using
      (tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (rate ^ 2)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLimit tendsto_const_nhds hLower hUpper
