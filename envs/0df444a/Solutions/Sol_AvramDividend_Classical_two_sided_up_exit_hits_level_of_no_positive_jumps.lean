-- Prove2me | solution 1 for AvramDividend.Classical.two_sided_up_exit_hits_level_of_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:12:42.645446+00:00
-- url     : https://prove2.me/submissions/e5a7097f-682e-44fc-a01a-73bdbae55376

import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- An upper exit preceding a lower exit is finite and creeps to its level
because a spectrally negative Lévy process has no upward jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) (ω : Ω)
    (hlt : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) = twoSidedExitUpTime X (a - x) ω ∧
      X.X t ω = a - x := by
  have hfinite : twoSidedExitUpTime X (a - x) ω ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact not_top_lt hlt
  let t : ℝ≥0 := (twoSidedExitUpTime X (a - x) ω).toNNReal
  have ht : (t : ℝ≥0∞) = twoSidedExitUpTime X (a - x) ω :=
    ENNReal.coe_toNNReal hfinite
  refine ⟨t, ht, ?_⟩
  exact firstUpcrossing_value_eq_threshold X (a - x)
    (sub_nonneg.mpr hxa) ω t (by simpa [twoSidedExitUpTime] using ht)
