-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_full_stopped_reward_le_killed_record_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:11:43.941577+00:00
-- url     : https://prove2.me/submissions/34b91c22-8ad7-451d-a1b1-a5bf13ba8422

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_lintegral_Ico_le_Ioc_of_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_stopped_finite_horizon_reward_le_killed_record_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by
  classical
  let ν := dividendMeasure (runningSup X) ω
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  let C : ℝ≥0∞ :=
    ∑' k : ℕ, if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
      ENNReal.ofReal
        (h * Real.exp (-(q *
          (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
    else 0
  change (∫⁻ r in paymentTimes τ, f r ∂ν) ≤ C
  by_cases hτzero : τ = 0
  · subst τ
    have hs : paymentTimes (0 : ℝ≥0∞) = ({0} : Set ℝ) := by
      simpa using paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞)
    rw [hs, setLIntegral_measure_zero ({0} : Set ℝ) f
      (runningSup_dividendMeasure_zero_atom X ω)]
    exact zero_le
  · have hτpos : 0 < τ := pos_iff_ne_zero.mpr hτzero
    apply paymentTimes_lintegral_le_of_rational_prefix_bounds ν f τ C hτpos
    intro z
    let t : ℝ≥0 := ⟨(z.1 : ℝ), le_of_lt z.property.1⟩
    have ht : (t : ℝ≥0∞) < τ := by
      rw [ENNReal.coe_nnreal_eq]
      exact z.property.2
    have hsubset : Ioc (0 : ℝ) (t : ℝ) ⊆ paymentTimes τ :=
      paymentTimes_Ioc_subset_of_terminal_survival
        τ (0 : ℝ) (t : ℝ) le_rfl z.property.2
    have hcut :
        (∫⁻ r in Ioc (0 : ℝ) (t : ℝ), f r ∂ν) ≤
        (∫⁻ r in paymentTimes τ,
          if r ∈ Ioc (0 : ℝ) (t : ℝ) then f r else 0 ∂ν) := by
      have hsame :
          (∫⁻ r in Ioc (0 : ℝ) (t : ℝ), f r ∂ν) =
          (∫⁻ r in Ioc (0 : ℝ) (t : ℝ),
            if r ∈ Ioc (0 : ℝ) (t : ℝ) then f r else 0 ∂ν) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        simp only [if_pos hr]
      calc
        (∫⁻ r in Ioc (0 : ℝ) (t : ℝ), f r ∂ν) =
            (∫⁻ r in Ioc (0 : ℝ) (t : ℝ),
              if r ∈ Ioc (0 : ℝ) (t : ℝ) then f r else 0 ∂ν) := hsame
        _ ≤ (∫⁻ r in paymentTimes τ,
          if r ∈ Ioc (0 : ℝ) (t : ℝ) then f r else 0 ∂ν) :=
            lintegral_mono_set hsubset
    calc
      (∫⁻ r in Ico (0 : ℝ) (z.1 : ℝ), f r ∂ν) ≤
          (∫⁻ r in Ioc (0 : ℝ) (t : ℝ), f r ∂ν) :=
        lintegral_Ico_le_Ioc_of_zero_initial_atom ν f (t : ℝ)
          (runningSup_dividendMeasure_zero_atom X ω)
      _ ≤ (∫⁻ r in paymentTimes τ,
        if r ∈ Ioc (0 : ℝ) (t : ℝ) then f r else 0 ∂ν) := hcut
      _ ≤ C := by
        dsimp [C, f, ν]
        exact stopped_finite_horizon_reward_le_killed_record_tsum
          X ω τ q h hq hh t ht
