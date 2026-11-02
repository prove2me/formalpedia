-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_discounted_C1_source_stopped_signed_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:23.17404+00:00
-- url     : https://prove2.me/submissions/ab9449fd-739a-47a7-aaeb-ebcb69e87aab

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One original-source event simultaneously gives the discounted C1
positive-cap source sign and an observable source-only absolute envelope
for those derivative-weighted remainder sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
        (M : ℝ) (hM : 0 ≤ M)
        (hcoef : ∀ i : ℕ,
          |Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)| ≤ M),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0 ∧
        |(Finset.range n).sum (fun i =>
          (Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i)))| ≤
          M * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
      X hBV x D hD w C hw_grad q,
      avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
      X hBV] with ω hsign hweighted
  obtain ⟨R, hRdef, hRmono, hstrip⟩ := hsign
  obtain ⟨Q, hQdef, hQmono, hbound⟩ := hweighted
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop hinterior M hM hcoef
  constructor
  · exact hstrip τ u hu n hstop hinterior
  · rw [hRQ]
    exact hbound u hu n
      (fun i => Real.exp (-(q * (u i : ℝ))) *
        deriv w (riskProcess X x D (u i) ω)) M hM hcoef
