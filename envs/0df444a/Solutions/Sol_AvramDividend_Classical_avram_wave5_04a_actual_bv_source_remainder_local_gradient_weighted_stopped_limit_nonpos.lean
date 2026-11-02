-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_limit_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:17.977323+00:00
-- url     : https://prove2.me/submissions/a09d7efa-ae93-43f5-aeae-c943814cec5a

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The nonpositive source residual contribution persists under real
limits of stopped, nonnegatively weighted local-gradient finite sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) :
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
        (a : ℕ → ℕ → ℝ) (ha : ∀ k i, 0 ≤ a k i)
        (hderiv : ∀ k (i : Fin (n k)),
          0 ≤ deriv w (riskProcess X x D (u k i) ω))
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(a k i * deriv w (riskProcess X x D (u k i) ω)) *
              (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos
      X hBV x D hD w] with ω hω
  obtain ⟨R, hRdef, hRmono, hsign⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop a ha hderiv L hlim
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun k =>
    hsign τ (u k) (hu k) (n k) (hstop k) (a k) (ha k) (hderiv k))
