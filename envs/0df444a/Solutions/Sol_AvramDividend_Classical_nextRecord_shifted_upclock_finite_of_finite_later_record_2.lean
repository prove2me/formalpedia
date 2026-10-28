-- Prove2me | solution 2 for AvramDividend.Classical.nextRecord_shifted_upclock_finite_of_finite_later_record
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:57:22.578535+00:00
-- url     : https://prove2.me/submissions/526ce866-f4f1-41a1-8485-5091e9a266e4

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b ε : ℝ) (hε : 0 ≤ ε) (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v) :
    (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) ≠ ⊤ := by 
  have h1 := nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt
  rw [← hv, ← hδ, ENNReal.coe_add] at h1
  rw [← (ENNReal.add_right_inj ENNReal.coe_ne_top).1 h1]
  exact ENNReal.coe_ne_top
