-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_budget_from_stopped_error_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:09:11.153074+00:00
-- url     : https://prove2.me/submissions/e68a580f-81db-4425-afd4-ef0614c685d8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_residual_grid_expected_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A genuine stopped source budget with zero-mean jump martingale,
    nonpositive HJB correction and actual BV residual implies strict cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) (hstop : ∀ ω, u n ≤ τ ω)
    (hResidualInt : Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal
      ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
        (V (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) -
          V (riskProcess X x D (u i) ω))) P)
    (T : ℝ) (hT : 0 ≤ T)
    (Mart HJB : Ω → ℝ)
    (hMartMean : (∫ ω, Mart ω ∂P) = 0)
    (hHJBMean : (∫ ω, HJB ω ∂P) ≤ 0)
    (hBudget :
      let S : ℝ≥0 := ⟨T, hT⟩
      let CashOpen : Ω → ℝ := fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
      let Pre : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
      let Corr : Ω → ℝ := fun ω =>
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) -
            (∑' (v : ℝ≥0),
              if 0 < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal
        ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
          (V (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i))) -
            V (riskProcess X x D (u i) ω))
      (∫ ω, CashOpen ω + Pre ω ∂P) ≤
        w x + (∫ ω, Mart ω ∂P) + (∫ ω, HJB ω ∂P) +
          (∫ ω, Corr ω ∂P)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
    (∫ ω, CashOpen ω + Pre ω ∂P) ≤ w x := by
  let Corr : Ω → ℝ := fun ω =>
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal
    ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
      (V (riskProcess X x D (u i) ω -
        (R (u (i + 1)) - R (u i))) -
        V (riskProcess X x D (u i) ω))
  have hCorr : (∫ ω, Corr ω ∂P) ≤ 0 := by
    simpa only [Corr] using
      (avram_p3_bv_original_residual_grid_expected_nonpos
        X hBV x D q C hC w V hw_cont hw0 hw_neg hw_smooth
        hw_grad hVtop hVfinite τ u hu n hstop hResidualInt)
  dsimp only at hBudget ⊢
  have hBound := hBudget
  rw [hMartMean] at hBound
  linarith
