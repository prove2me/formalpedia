-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_lower_geometric_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:45:10.580352+00:00
-- url     : https://prove2.me/submissions/af27e38d-1983-4504-b13a-c4de37225d48

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_ge_scalar_geometric_tsum
import Theorems.Thm_AvramDividend_Classical_firstRecord_ofReal_geometric_tsum
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    ENNReal.ofReal ε *
      (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) ≤
      (∑' n : ℕ, (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by
  calc
    ENNReal.ofReal ε *
        (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
      (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) := by
        exact (firstRecord_ofReal_geometric_tsum ε p (le_of_lt hε) hp).symm
    _ ≤ (∑' n : ℕ, (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :=
      chat12_total_expected_lower_ge_scalar_geometric_tsum
        X q a ε ha hε p hp hExit
