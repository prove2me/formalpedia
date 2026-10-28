-- Prove2me | solution 1 for AvramDividend.Classical.chat04_up_exit_time_zero_of_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:33:07.78653+00:00
-- url     : https://prove2.me/submissions/e08716a1-66af-43a1-9f45-cfdd1c12f6b2

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitUpTime X 0 ω = 0 := by
  apply le_antisymm ?_ bot_le
  by_contra hn
  have hpos : (0 : ℝ≥0∞) < twoSidedExitUpTime X 0 ω :=
    lt_of_not_ge hn
  obtain ⟨ε, hε0, hεExit⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hεpos : (0 : ℝ≥0) < ε := by
    exact_mod_cast hε0
  obtain ⟨t, htε, hXt⟩ := hNear ε hεpos
  have hLe : twoSidedExitUpTime X 0 ω ≤ (t : ℝ≥0∞) := by
    change (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω),
      (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞)
    have hOuter :
        (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω),
          (s : ℝ≥0∞)) ≤
        (⨅ (_ : (0 : ℝ) < X.X t ω), (t : ℝ≥0∞)) :=
      iInf_le
        (fun s : ℝ≥0 => ⨅ (_ : (0 : ℝ) < X.X s ω),
          (s : ℝ≥0∞)) t
    have hInner :
        (⨅ (_ : (0 : ℝ) < X.X t ω), (t : ℝ≥0∞)) ≤
        (t : ℝ≥0∞) :=
      iInf_le (fun (_ : (0 : ℝ) < X.X t ω) => (t : ℝ≥0∞)) hXt
    exact hOuter.trans hInner
  have htε' : (t : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast htε
  exact lt_asymm hεExit (lt_of_le_of_lt hLe htε')
