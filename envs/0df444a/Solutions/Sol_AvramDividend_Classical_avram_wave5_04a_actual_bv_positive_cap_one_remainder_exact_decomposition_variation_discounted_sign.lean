-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:03:49.880015+00:00
-- url     : https://prove2.me/submissions/4d92e886-39e1-4cfa-a74e-799e87f19595

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete Chat03 source-only interface on one original BV sample:
exact intrinsic left-jump decomposition, exact residual total variation,
and nonpositive stopped discounted HJB interior-gradient contribution.
No controlled nonlinear Ito-Meyer integration is assumed. -/
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
      (∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (v : ℝ≥0),
              if s < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal -
            (R t - R s)) ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0)) ∧
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV,
      avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
      X hBV,
      avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
      X hBV x D hD w C hw_grad q]
    with ω hsource hvariation hdiscounted
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  obtain ⟨Q, hQdef, hQmono, hvar⟩ := hvariation
  obtain ⟨S, hSdef, hSmono, hsign⟩ := hdiscounted
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  have hRS : R = S := by
    funext t
    exact (hRdef t).trans (hSdef t).symm
  refine ⟨R, hRdef, hRmono, hinterval, ?_, ?_⟩
  · rw [hRQ]
    exact hvar
  · intro τ u hu n hstop hinterior
    rw [hRS]
    exact hsign τ u hu n hstop hinterior
