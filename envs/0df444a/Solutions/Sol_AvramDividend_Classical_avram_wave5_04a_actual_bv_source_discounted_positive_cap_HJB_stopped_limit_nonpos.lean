-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:03:45.244312+00:00
-- url     : https://prove2.me/submissions/e465b3ba-c5d9-43fa-bc35-b96c4b7d13c4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every real limit of stopped, exponentially discounted original BV
source-residual C1 sums is nonpositive while all sampled reserves lie
in the positive-cap HJB gradient region. No Ito-Meyer identification. -/
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
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (hinterior : ∀ k (i : Fin (n k)),
          0 < riskProcess X x D (u k i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u k i) ω) < C)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(Real.exp (-(q * (u k i : ℝ))) *
              deriv w (riskProcess X x D (u k i) ω)) *
                (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
      X hBV x D hD w C hw_grad q] with ω hω
  obtain ⟨R, hRdef, hRmono, hsign⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop hinterior L hlim
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun k =>
    hsign τ (u k) (hu k) (n k) (hstop k) (hinterior k))
