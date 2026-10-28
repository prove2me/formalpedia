-- Prove2me | solution 1 for AvramDividend.Classical.laplace_large_deficit_probability_bound_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:57:30.644428+00:00
-- url     : https://prove2.me/submissions/26d63e86-773c-4a92-86da-af3f483550ca

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter

/-- A nonnegative random deficit has a large-value tail controlled by
    the loss of its Laplace transform from total measure. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hD : ∀ ω, 0 ≤ D ω)
    (hLargeMeas : MeasurableSet {ω : Ω | a ≤ D ω})
    (hLeft : Integrable
      (fun ω => if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0) μ)
    (hGap : Integrable (fun ω => (1 : ℝ) - Real.exp (-D ω)) μ)
    (hOne : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    (hExp : Integrable (fun ω => Real.exp (-D ω)) μ) :
    (1 - Real.exp (-a)) * μ.real {ω : Ω | a ≤ D ω} ≤
      μ.real Set.univ - (∫ ω, Real.exp (-D ω) ∂μ) := by
  classical
  have hPoint (ω : Ω) :
      (if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0) ≤
        1 - Real.exp (-D ω) := by
    by_cases hLarge : a ≤ D ω
    · simp only [if_pos hLarge]
      have hexp : Real.exp (-D ω) ≤ Real.exp (-a) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    · simp only [if_neg hLarge]
      have hexp : Real.exp (-D ω) ≤ (1 : ℝ) := by
        calc
          Real.exp (-D ω) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by linarith [hD ω])
          _ = 1 := Real.exp_zero
      linarith
  have hLargeIntegral :
      (∫ ω, if a ≤ D ω then (1 : ℝ) else 0 ∂μ) =
        μ.real {ω : Ω | a ≤ D ω} := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one hLargeMeas)
  have hScale :
      (∫ ω, if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0 ∂μ) =
        (1 - Real.exp (-a)) * μ.real {ω : Ω | a ≤ D ω} := by
    have hmul (ω : Ω) :
        (if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0) =
          (1 - Real.exp (-a)) * (if a ≤ D ω then (1 : ℝ) else 0) := by
      by_cases h : a ≤ D ω <;> simp [h]
    calc
      (∫ ω, if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0 ∂μ) =
          ∫ ω, (1 - Real.exp (-a)) *
            (if a ≤ D ω then (1 : ℝ) else 0) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hmul)
      _ = (1 - Real.exp (-a)) *
          (∫ ω, if a ≤ D ω then (1 : ℝ) else 0 ∂μ) :=
        integral_const_mul _ _
      _ = (1 - Real.exp (-a)) * μ.real {ω : Ω | a ≤ D ω} := by
        rw [hLargeIntegral]
  have hGapIntegral :
      (∫ ω, (1 : ℝ) - Real.exp (-D ω) ∂μ) =
        μ.real Set.univ - (∫ ω, Real.exp (-D ω) ∂μ) := by
    simp [integral_sub hOne hExp]
  calc
    (1 - Real.exp (-a)) * μ.real {ω : Ω | a ≤ D ω} =
        (∫ ω, if a ≤ D ω then (1 - Real.exp (-a) : ℝ) else 0 ∂μ) :=
      hScale.symm
    _ ≤ (∫ ω, (1 : ℝ) - Real.exp (-D ω) ∂μ) :=
      integral_mono_ae hLeft hGap (Filter.Eventually.of_forall hPoint)
    _ = μ.real Set.univ - (∫ ω, Real.exp (-D ω) ∂μ) :=
      hGapIntegral
