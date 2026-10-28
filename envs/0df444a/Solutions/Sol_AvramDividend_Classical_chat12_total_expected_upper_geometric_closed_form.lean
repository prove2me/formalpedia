-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_upper_geometric_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:48:15.431514+00:00
-- url     : https://prove2.me/submissions/93462f16-7be1-4809-8205-20010499711b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_le_scalar_geometric_tsum
import Theorems.Thm_AvramDividend_Classical_chat12_ofReal_geometric_tsum_unshifted
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
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) ≤
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by
  calc
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) ≤
        (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) :=
          chat12_total_expected_upper_le_scalar_geometric_tsum
            X hX q hq a ε ha hε p hp hExit
    _ = ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ :=
          chat12_ofReal_geometric_tsum_unshifted ε p hε.le hp
