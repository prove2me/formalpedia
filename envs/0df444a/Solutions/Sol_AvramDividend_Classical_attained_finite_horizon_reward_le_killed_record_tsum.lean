-- Prove2me | solution 1 for AvramDividend.Classical.attained_finite_horizon_reward_le_killed_record_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:51:36.787139+00:00
-- url     : https://prove2.me/submissions/78d3fba2-b802-4d9d-955c-7a8ae7e952ca

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_runningSup_full_finite_horizon_last_record_budget
import Theorems.Thm_AvramDividend_Classical_surviving_record_prefix_budget_le_killed_tsum
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by
  obtain ⟨u, hu, hbudget⟩ :=
    runningSup_full_finite_horizon_last_record_budget
      X ω τ q h hq hh N t hN hnext htτ
  let c : ℕ → ℝ≥0∞ := fun k =>
    ⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)
  have hc : ∀ k : ℕ, k ≤ N → c k = (u k : ℝ≥0∞) := by
    intro k hk
    exact (hu k hk).symm
  have hmono : ∀ k : ℕ, k ≤ N → c k ≤ c N := by
    intro k hk
    apply firstUpcrossing_threshold_iInf_mono X ω
    have hkn : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    simpa only [zero_add] using
      (mul_le_mul_of_nonneg_right hkn (le_of_lt hh))
  have hSurvive : (u N : ℝ≥0∞) < τ := by
    calc
      (u N : ℝ≥0∞) = c N := hu N le_rfl
      _ < (t : ℝ≥0∞) := hN
      _ < τ := htτ
  have hprefix :=
    surviving_record_prefix_budget_le_killed_tsum
      τ q h (le_of_lt hh) c u N hc hmono hSurvive
  have hpath := le_trans hbudget hprefix
  simpa only [c, zero_add, chat08_named_upper_clock_eq_raw_infimum]
    using hpath
