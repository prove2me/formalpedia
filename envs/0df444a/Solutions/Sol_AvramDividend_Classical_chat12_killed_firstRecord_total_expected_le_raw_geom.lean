-- Prove2me | solution 1 for AvramDividend.Classical.chat12_killed_firstRecord_total_expected_le_raw_geom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:34:04.925667+00:00
-- url     : https://prove2.me/submissions/9439371b-3150-4dc3-9739-78708a825a48

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_raw_upper_geometric
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
        else 0 ∂P)) ≤
      (∑' n : ℕ, (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) ^ n * (∫⁻ ω, if twoSidedExitUpTime X ((0 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((0 : ℝ) * ε) ω).toReal)))
        else 0 ∂P)) := by
  apply ENNReal.tsum_le_tsum
  intro n
  exact chat12_killed_firstRecord_raw_upper_geometric
    X hX q hq a ε ha hε n
