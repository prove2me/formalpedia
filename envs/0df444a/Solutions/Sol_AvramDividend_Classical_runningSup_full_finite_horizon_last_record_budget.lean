-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_full_finite_horizon_last_record_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:26:51.468987+00:00
-- url     : https://prove2.me/submissions/f0a5b0e8-801e-4c53-8ac8-a18733f77243

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_last_record_stopped_upper
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_initial_record_zero
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Mathlib.Analysis.Complex.Exponential

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
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω),
            (r : ℝ≥0∞))) ∧
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ∑ k ∈ Finset.range (N + 1),
        ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
          ENNReal.ofReal h := by
  obtain ⟨u, hu, hbudget⟩ :=
    runningSup_finite_horizon_last_record_stopped_upper
      X ω τ q 0 h hq (by exact le_refl 0) hh N t hN hnext htτ
  have hlevel : (0 : ℝ) ≤ (N : ℝ) * h :=
    mul_nonneg (Nat.cast_nonneg N) (le_of_lt hh)
  have hmono :
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞)) ≤
      (⨅ (r : ℝ≥0)
        (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω),
        (r : ℝ≥0∞)) := by
    apply firstUpcrossing_threshold_iInf_mono X ω
    simpa using hlevel
  have hfirst : (u 0 : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω),
        (r : ℝ≥0∞)) := by
    simpa using (hu 0 (Nat.zero_le N))
  have hut : (u 0 : ℝ≥0∞) < (t : ℝ≥0∞) := by
    rw [hfirst]
    exact lt_of_le_of_lt hmono hN
  have hutNN : u 0 ≤ t :=
    ENNReal.coe_le_coe.mp (le_of_lt hut)
  have hutReal : (u 0 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hutNN
  have h0 : (0 : ℝ) ≤ (u 0 : ℝ) := by
    exact_mod_cast (show (0 : ℝ≥0) ≤ u 0 by exact zero_le)
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  have hzero :
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (0 : ℝ) (u 0 : ℝ) then f r else 0
        ∂(dividendMeasure (runningSup X) ω)) = 0 :=
    stopped_lintegral_initial_record_zero X ω τ f (u 0) hfirst
  have hsplit :=
    stopped_lintegral_Ioc_adjacent_add
      (dividendMeasure (runningSup X) ω) (paymentTimes τ)
      f 0 (u 0 : ℝ) (t : ℝ) h0 hutReal
  refine ⟨u, hu, ?_⟩
  calc
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ r in paymentTimes τ,
          if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ) then f r else 0
          ∂(dividendMeasure (runningSup X) ω)) := by
            rw [hsplit, hzero, zero_add]
    _ ≤ _ := hbudget
