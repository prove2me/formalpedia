-- Prove2me | solution 1 for AvramDividend.Classical.stopped_firstRecord_survived_prefix_discount_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:48:54.088029+00:00
-- url     : https://prove2.me/submissions/a9a0a4d7-9bc3-4967-8824-726edfdd6e78

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_lower_bound
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_uniform_record_grid_mono
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

/-! Transfer finite attained-clock Stieltjes bounds to surviving named record clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ) (hq : 0 ≤ q)
    (hb : 0 ≤ b) (hh : 0 < h) (N : ℕ)
    (hSurvive : twoSidedExitUpTime X (b + (N : ℝ) * h) ω < τ) :
    (∑ k ∈ Finset.range N,
      ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X (b + ((k + 1 : ℕ) : ℝ) * h) ω).toReal))) *
      ENNReal.ofReal h) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc
          (twoSidedExitUpTime X (b + (0 : ℝ) * h) ω).toReal
          (twoSidedExitUpTime X (b + (N : ℝ) * h) ω).toReal
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) := by
  let T : ℕ → ℝ≥0∞ :=
    fun k => twoSidedExitUpTime X (b + (k : ℝ) * h) ω
  let u : ℕ → ℝ≥0 := fun k => (T k).toNNReal
  have hmono : Monotone T := by
    simpa only [T, chat08_named_upper_clock_eq_raw_infimum] using
      firstUpcrossing_uniform_record_grid_mono X ω b h (le_of_lt hh)
  have hfin (k : ℕ) (hk : k ≤ N) : T k ≠ ⊤ := by
    have ht : T k < ⊤ :=
      lt_of_le_of_lt (hmono hk) (lt_of_lt_of_le hSurvive le_top)
    exact ne_of_lt ht
  have hcoe (k : ℕ) (hk : k ≤ N) : (u k : ℝ≥0∞) = T k := by
    simpa only [u] using (ENNReal.coe_toNNReal (hfin k hk))
  have hpass (k : ℕ) (hk : k ≤ N) :
      (u k : ℝ≥0∞) =
        (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω),
          (r : ℝ≥0∞)) := by
    rw [hcoe k hk]
    exact chat08_named_upper_clock_eq_raw_infimum X (b + (k : ℝ) * h) ω
  have hord (k : ℕ) (hk : k < N) : (u k : ℝ) ≤ (u (k + 1) : ℝ) := by
    have hle : (u k : ℝ≥0∞) ≤ (u (k + 1) : ℝ≥0∞) := by
      rw [hcoe k (Nat.le_of_lt hk), hcoe (k + 1) (Nat.succ_le_of_lt hk)]
      exact hmono (Nat.le_succ k)
    exact_mod_cast (ENNReal.coe_le_coe.mp hle)
  have hSurvive' : ENNReal.ofReal (u N : ℝ) < τ := by
    simpa only [ENNReal.ofReal_coe_nnreal, hcoe N le_rfl] using hSurvive
  have hbound :=
    runningSup_N_record_cells_discount_lower_bound
      X ω τ q hq b h hb (le_of_lt hh) N u hpass hord hSurvive'
  convert hbound using 1 <;>
    simp [u, T, ENNReal.coe_toNNReal_eq_toReal]
