-- Prove2me | solution 1 for AvramDividend.Classical.stopped_dividend_payment_partition_lintegral_eq_iSup_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:52:50.615988+00:00
-- url     : https://prove2.me/submissions/72ad4ef9-c52d-48c0-8736-94090a268405

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A stopped discounted Stieltjes dividend payout is the increasing
    supremum of exact payments over any countable disjoint measurable
    partition. It includes continuous dividends and every dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0∞) (T q : ℝ) (ω : Ω)
    (S : ℕ → Set ℝ)
    (hMeas : ∀ k, MeasurableSet (S k))
    (hDisjoint : Pairwise (Function.onFun Disjoint S))
    (hCover : (⋃ k : ℕ, S k) = paymentTimes σ ∩ Iic T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ∑ k ∈ Finset.range n,
        ∫⁻ t in S k,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) := by
  calc
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        ∑' k : ℕ, ∫⁻ t in S k,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) := by
            rw [← hCover]
            exact MeasureTheory.lintegral_iUnion hMeas hDisjoint
              (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
    _ = ⨆ n : ℕ, ∑ k ∈ Finset.range n,
        ∫⁻ t in S k,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) :=
      ENNReal.tsum_eq_iSup_nat
