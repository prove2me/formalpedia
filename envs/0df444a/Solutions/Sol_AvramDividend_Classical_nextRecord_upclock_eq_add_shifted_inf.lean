-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_upclock_eq_add_shifted_inf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:27:33.868455+00:00
-- url     : https://prove2.me/submissions/86f434ba-be7d-4e11-80b1-2616c67c2a15

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_shifted_inf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Extract the past clock as an additive shift of a future first passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b) :
    twoSidedExitUpTime X (b + ε) ω =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0)
          (_ : ε < X.X (u + t) ω - X.X u ω),
          (t : ℝ≥0∞)) := by
  rw [nextRecord_upclock_eq_shifted_inf X b ε hε u ω hu hAt]
  rw [ENNReal.add_iInf₂]
  simp only [ENNReal.coe_add]
