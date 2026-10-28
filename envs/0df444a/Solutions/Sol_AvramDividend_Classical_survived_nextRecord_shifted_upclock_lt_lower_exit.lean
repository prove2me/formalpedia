-- Prove2me | solution 1 for AvramDividend.Classical.survived_nextRecord_shifted_upclock_lt_lower_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:51:42.16048+00:00
-- url     : https://prove2.me/submissions/444afb2d-9581-4616-9a71-57665eba1a06

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Theorems.Thm_AvramDividend_Classical_levy_shifted_exit_strict_order_of_finite_weak_order
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! A finite surviving record forces strict future upper-before-lower exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
    (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := by
  classical
  let U : ℝ≥0∞ := ⨅ (t : ℝ≥0)
    (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)
  have hclock : (v : ℝ≥0∞) = (u : ℝ≥0∞) + U := by
    calc
      (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω := hv
      _ = (u : ℝ≥0∞) + U := by
        simpa only [U] using
          nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt
  have hFinite : U ≠ ⊤ := by
    intro h
    simp [h] at hclock
  have hLe := survived_nextRecord_shifted_upclock_le_lower_exit
    X ω a b ε ha hb hε u v δ hu hAt hv hδ hSurvive
  have hsep : -a < ε :=
    lt_of_lt_of_le (neg_lt_zero.mpr ha) hε
  exact levy_shifted_exit_strict_order_of_finite_weak_order
    X ω u (-a) ε hsep hFinite (by simpa only [U] using hLe)
