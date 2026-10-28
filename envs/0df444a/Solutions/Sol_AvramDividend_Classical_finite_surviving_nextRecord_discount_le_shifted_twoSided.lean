-- Prove2me | solution 1 for AvramDividend.Classical.finite_surviving_nextRecord_discount_le_shifted_twoSided
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:54:47.465402+00:00
-- url     : https://prove2.me/submissions/7c2aeb0a-c273-4571-a35c-ce11eebfe68b

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_lt_lower_exit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Finite surviving records have no stronger killed payoff than two-sided exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v) :
    (if twoSidedExitUpTime X (b + ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if (⨅ (t : ℝ≥0)
              (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0)
              (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞))
        then ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0)
              (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))))
        else 0)) := by
  classical
  let U : ℝ≥0∞ := ⨅ (t : ℝ≥0)
    (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)
  let D : ℝ≥0∞ := ⨅ (t : ℝ≥0)
    (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)
  have hclock : (v : ℝ≥0∞) = (u : ℝ≥0∞) + U := by
    calc
      (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω := hv
      _ = (u : ℝ≥0∞) + U := by
        simpa only [U] using
          nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt
  have hFinite : U ≠ ⊤ := by
    intro h
    simp [h] at hclock
  apply killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
    X a b ε q hε ω u hu hAt U D (by rfl) hFinite
  intro hs
  have hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω := by
    simpa only [hv] using hs
  exact survived_nextRecord_shifted_upclock_lt_lower_exit
    X ω a b ε ha hb hε u v δ hu hAt hv hδ hSurvive
