-- Prove2me | solution 1 for AvramDividend.Classical.chat04_down_exit_time_zero_of_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:54:11.637282+00:00
-- url     : https://prove2.me/submissions/fbd9fd52-d866-49f2-8dd5-728bcf0b6155

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) = 0 := by
  apply le_antisymm ?_ bot_le
  by_contra hn
  have hpos :
      (0 : ℝ≥0∞) <
        (⨅ (s : ℝ≥0) (_ : X.X s ω < 0), (s : ℝ≥0∞)) :=
    lt_of_not_ge hn
  obtain ⟨ε, hε0, hεExit⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hεpos : (0 : ℝ≥0) < ε := by
    exact_mod_cast hε0
  obtain ⟨t, htε, hXt⟩ := hNear ε hεpos
  have hLe :
      (⨅ (s : ℝ≥0) (_ : X.X s ω < 0), (s : ℝ≥0∞)) ≤
      (t : ℝ≥0∞) := by
    have hOuter :
        (⨅ (s : ℝ≥0) (_ : X.X s ω < 0), (s : ℝ≥0∞)) ≤
        (⨅ (_ : X.X t ω < 0), (t : ℝ≥0∞)) :=
      iInf_le
        (fun s : ℝ≥0 => ⨅ (_ : X.X s ω < 0), (s : ℝ≥0∞)) t
    have hInner :
        (⨅ (_ : X.X t ω < 0), (t : ℝ≥0∞)) ≤
        (t : ℝ≥0∞) :=
      iInf_le (fun (_ : X.X t ω < 0) => (t : ℝ≥0∞)) hXt
    exact hOuter.trans hInner
  have htε' : (t : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast htε
  exact lt_asymm hεExit (lt_of_le_of_lt hLe htε')
