-- Prove2me | solution 3 for AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:56:25.502154+00:00
-- url     : https://prove2.me/submissions/4e995760-24db-410c-ae6b-1ddb2510304e

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_lt_lower_exit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Compose strict surviving-record exit order with pathwise discounted weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by
  have hIncl : twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω → ρ < σ := by
    intro hs
    have hsv : (v : ℝ≥0∞) < barrierRuinTime X a ω :=
      lt_of_eq_of_lt hv hs
    have h := survived_nextRecord_shifted_upclock_lt_lower_exit
      X ω a b ε ha hb hε u v δ hu hAt hv hδ hsv
    simpa only [← hρ, ← hσ] using h
  exact killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
    X a b ε q hε ω u hu hAt ρ σ hρ hρfinite hIncl
