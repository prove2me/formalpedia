-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_variation_and_stopped_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:45:24.992192+00:00
-- url     : https://prove2.me/submissions/2395aaa0-ce4e-45e9-87a6-342159f21b59

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The single original BV source residual, on one almost-sure event,
has exact intrinsic left-jump increments, exact variation, and stopped
monotone C1 residual limits that are nonpositive. No Ito-Meyer identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Monotone w) :
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
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(deriv w (riskProcess X x D (u k i) ω)) *
              (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder X hBV,
      avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact X hBV,
      avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos X hBV x D hD w hw]
    with ω hsource hvariation hlimit
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  obtain ⟨Q, hQdef, hQmono, hvar⟩ := hvariation
  obtain ⟨S, hSdef, hSmono, hsignlim⟩ := hlimit
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  have hRS : R = S := by
    funext t
    exact (hRdef t).trans (hSdef t).symm
  refine ⟨R, hRdef, hRmono, hinterval, ?_, ?_⟩
  · rw [hRQ]
    exact hvar
  · intro τ u hu n hstop L hconv
    rw [hRS] at hconv
    exact hsignlim τ u hu n hstop L hconv
