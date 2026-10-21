-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_firstRecord_step_discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:20:08.468871+00:00
-- url     : https://prove2.me/submissions/758731ce-406b-468e-8564-43eacf2cadbb

import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_between_attained_record_levels
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hSurvive : ENNReal.ofReal (v : ℝ) < τ) :
    (ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (v : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (v : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h) := by
  have hInterval : Set.Ioc (u : ℝ) (v : ℝ) ⊆ paymentTimes τ :=
    paymentTimes_Ioc_subset_of_terminal_survival τ (u : ℝ) (v : ℝ)
      (NNReal.coe_nonneg u) hSurvive
  have hMass := runningSup_dividendMeasure_between_attained_record_levels
    X b h hb hh ω u v hu hv
  have hIncrement :
      ENNReal.ofReal
        (runningSup X ((v : ℝ).toNNReal) ω -
         runningSup X ((u : ℝ).toNNReal) ω) = ENNReal.ofReal h := by
    exact (runningSup_dividendMeasure_Ioc_eq_record_increment
      X ω (u : ℝ) (v : ℝ)).symm.trans hMass
  have hbnd := runningSup_stopped_Ioc_discount_record_bounds_of_survival
    X ω τ q hq (u : ℝ) (v : ℝ) hInterval
  simpa only [hIncrement] using hbnd
