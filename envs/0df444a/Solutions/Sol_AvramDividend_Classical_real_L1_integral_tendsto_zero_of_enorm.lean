-- Prove2me | solution 1 for AvramDividend.Classical.real_L1_integral_tendsto_zero_of_enorm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:02:03.687993+00:00
-- url     : https://prove2.me/submissions/1b9439db-4f8d-4228-b27d-22d7bd630393

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ)
    (hI : ∀ n, Integrable (F n) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫⁻ ω, ‖F n ω‖ₑ ∂P) atTop (nhds 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |F n ω| ∂P) atTop (nhds 0) := by
  have hconv :
      Tendsto (fun n : ℕ => (∫⁻ ω, ‖F n ω‖ₑ ∂P).toReal)
        atTop (nhds (0 : ℝ)) := by
    have hc : Tendsto ENNReal.toReal
        (nhds (0 : ℝ≥0∞)) (nhds (0 : ℝ)) := by
      simpa using (ENNReal.tendsto_toReal
        (by simp : (0 : ℝ≥0∞) ≠ ∞))
    exact hc.comp hlim
  have heq (n : ℕ) :
      (∫ ω, |F n ω| ∂P) =
        (∫⁻ ω, ‖F n ω‖ₑ ∂P).toReal := by
    have hnorm := ofReal_integral_norm_eq_lintegral_enorm (hI n)
    have hnonneg : 0 ≤ (∫ ω, |F n ω| ∂P) :=
      integral_nonneg (fun ω => abs_nonneg _)
    have h := congrArg ENNReal.toReal hnorm
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hnonneg] using h
  have hfun :
      (fun n : ℕ => ∫ ω, |F n ω| ∂P) =
        (fun n : ℕ => (∫⁻ ω, ‖F n ω‖ₑ ∂P).toReal) := by
    funext n
    exact heq n
  rw [hfun]
  exact hconv