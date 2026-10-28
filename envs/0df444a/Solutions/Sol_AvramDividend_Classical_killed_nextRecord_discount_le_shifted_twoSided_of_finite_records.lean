-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:04:17.490866+00:00
-- url     : https://prove2.me/submissions/fa38da81-372a-433b-bddc-e5aebc3723b9

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
import Theorems.Thm_AvramDividend_Classical_nextRecord_shifted_upclock_finite_of_finite_later_record
import Mathlib.Analysis.Complex.Exponential
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
      (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞))) :
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
  have hρfinite : ρ ≠ ⊤ := by
    rw [hρ]
    exact nextRecord_shifted_upclock_finite_of_finite_later_record
      X ω b ε hε u v δ hu hAt hv hδ
  exact killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
    X ω a b ε q ha hb hε u v δ hu hAt hv hδ ρ σ hρ hσ hρfinite
