-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_paymentTimes_iInter_boundary_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:48:09.201406+00:00
-- url     : https://prove2.me/submissions/5b53316c-c500-4a33-b02e-9aff364b1e81

import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_paymentTimes_iInter_diff_iInf_subset_terminal
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Shrinking payment windows can lose only a Stieltjes-null terminal point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) :
    (dividendMeasure (runningSup X) ω)
      ((⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n)) = 0 := by
  let τ : ℝ≥0∞ := ⨅ n, σ n
  have hsubset :
      (⋂ n, paymentTimes (σ n)) \
          paymentTimes τ ⊆ ({τ.toReal} : Set ℝ) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      have hn : t ∈ paymentTimes (σ 0) :=
        (Set.mem_iInter.mp ht.1) 0
      exact hn.1
    have heq : ENNReal.ofReal t = τ :=
      paymentTimes_iInter_diff_iInf_subset_terminal σ ht
    have hreal : t = τ.toReal := by
      calc
        t = (ENNReal.ofReal t).toReal := (ENNReal.toReal_ofReal ht0).symm
        _ = τ.toReal := congrArg ENNReal.toReal heq
    exact hreal
  have hzero :
      (dividendMeasure (runningSup X) ω) ({τ.toReal} : Set ℝ) = 0 :=
    runningSup_dividendMeasure_no_nonnegative_atoms X ω τ.toReal
      (by positivity)
  exact measure_mono_null hsubset hzero
