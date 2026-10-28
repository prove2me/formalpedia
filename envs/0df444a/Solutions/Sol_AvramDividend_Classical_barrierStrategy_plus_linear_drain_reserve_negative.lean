-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_plus_linear_drain_reserve_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:39:59.990919+00:00
-- url     : https://prove2.me/submissions/4926f278-71b8-4d79-9a37-a3aac06255c7

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A linear dividend drain added to the zero-barrier control immediately
    makes every strictly positive-time reserve negative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x) :
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      riskProcess X x
        (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω < 0 := by
  intro ω t ht
  have hc : ENNReal.ofReal
      (riskProcess X x (barrierStrategy X x 0) t ω) ≤ 0 := by
    simpa using
      (barrierStrategy_reserve_cap_bound_all_capital X x 0 hx le_rfl ω t ht)
  have hb : riskProcess X x (barrierStrategy X x 0) t ω ≤ 0 := by
    by_contra hn
    have hp : 0 < riskProcess X x (barrierStrategy X x 0) t ω :=
      lt_of_not_ge hn
    have he : (0 : ℝ≥0∞) < ENNReal.ofReal
        (riskProcess X x (barrierStrategy X x 0) t ω) :=
      ENNReal.ofReal_pos.mpr hp
    exact (not_lt_of_ge hc) he
  have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  change x + X.X t ω - (barrierStrategy X x 0 t ω + (t : ℝ)) < 0
  dsimp [riskProcess] at hb
  linarith
