-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_one_event_source_residual_and_controlled_reserve_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:22:28.606285+00:00
-- url     : https://prove2.me/submissions/f6a8f343-e2da-47e9-a2b8-db2872f66eab

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One samplewise event supports both the exact source BV remainder and
the actual controlled reserve's finite-partition variation, while keeping
source left jumps separate from chronological right dividend payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
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
              (R (u (i + 1)) - R (u i))) ≤ 0) ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n,
          |riskProcess X x D (u (i + 1)) ω -
            riskProcess X x D (u i) ω|) ≤
          2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
            (X.X (u n) ω - X.X (u 0) ω) +
            (D (u n) ω - D (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
      X hBV x D hD w C hw_grad q,
      avram_wave3_03_bv_controlled_reserve_partition_variation
      X hX hBV x D hD] with ω hsource hcontrolled
  obtain ⟨R, hRdef, hRmono, hinterval, hvariation, hsign⟩ := hsource
  refine ⟨R, hRdef, hRmono, hinterval, hvariation, hsign, ?_⟩
  intro u hu n
  exact hcontrolled u hu n
