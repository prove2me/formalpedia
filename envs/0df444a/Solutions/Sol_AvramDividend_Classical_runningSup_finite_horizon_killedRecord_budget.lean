-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_finite_horizon_killedRecord_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:42:17.391785+00:00
-- url     : https://prove2.me/submissions/efa18515-4570-4f80-90e4-675be3438c6c

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_full_finite_horizon_last_record_budget
import Theorems.Thm_AvramDividend_Classical_surviving_record_prefix_budget_le_killed_tsum
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-! Extend the finite-horizon Stieltjes budget to all killed record weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (((N + 1 : ℕ)) : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by
  classical
  let c : ℕ → ℝ≥0∞ := fun k =>
    ⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)
  obtain ⟨u, hu, hbudget⟩ :=
    runningSup_full_finite_horizon_last_record_budget
      X ω τ q h hq hh N t hN hnext htτ
  have hc (k : ℕ) (hk : k ≤ N) : c k = (u k : ℝ≥0∞) :=
    (hu k hk).symm
  have hmono (k : ℕ) (hk : k ≤ N) : c k ≤ c N := by
    apply firstUpcrossing_threshold_iInf_mono X ω
    simpa only [zero_add] using
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk : (k : ℝ) ≤ N) hh.le)
  have hSurvive : (u N : ℝ≥0∞) < τ := by
    calc
      (u N : ℝ≥0∞) = c N := hu N le_rfl
      _ < (t : ℝ≥0∞) := hN
      _ < τ := htτ
  have hsum := surviving_record_prefix_budget_le_killed_tsum
    τ q h hh.le c u N hc hmono hSurvive
  exact hbudget.trans (by simpa only [c] using hsum)
