-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_residual_grid_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:53:06.308123+00:00
-- url     : https://prove2.me/submissions/38500e94-87dd-452f-8d12-5ed5130f27fb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_global_source_residual_boundary_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine original BV downward source residual has nonpositive
    expected discounted finite-grid correction, including boundary contact. -/
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
    (hInt : Integrable (fun ω =>
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
          V (riskProcess X x D (u i) ω))) P) :
    (∫ ω,
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
          V (riskProcess X x D (u i) ω)) ∂P) ≤ 0 := by
  let R : Ω → ℝ≥0 → ℝ := fun ω t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
  let F : Ω → ℝ := fun ω =>
    ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
      (V (riskProcess X x D (u i) ω -
        (R ω (u (i + 1)) - R ω (u i))) -
        V (riskProcess X x D (u i) ω))
  have hsource := avram_p3_bv_global_source_residual_boundary_sign
    X hBV x D q C hC w V hw_cont hw0 hw_neg hw_smooth
      hw_grad hVtop hVfinite
  have hsign : ∀ᵐ ω ∂P, F ω ≤ 0 := by
    filter_upwards [hsource] with ω hω
    obtain ⟨R', hReq, _, hsum⟩ := hω
    have hR : R' = R ω := by
      funext t
      simpa only [R] using hReq t
    simpa only [F, hR] using hsum τ u hu n (hstop ω)
  change (∫ ω, F ω ∂P) ≤ 0
  exact integral_nonpos_of_ae hsign
