-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_measure_decomposition_and_discounted_stopped_C1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:49:42.041446+00:00
-- url     : https://prove2.me/submissions/2f274038-3ffb-4046-8773-cad6f6636aee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One almost-sure original BV source residual simultaneously gives
the exact physical intrinsic measure decomposition and the nonpositive
discounted stopped C1 contribution on the positive-cap HJB interior. -/
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
      (∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s)) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV,
      avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
      X hBV x D hD w C hw_grad q] with ω hsource hsign
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  obtain ⟨Q, hQdef, hQmono, hstrip⟩ := hsign
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  refine ⟨R, hRdef, hRmono, ?_, ?_⟩
  · intro s t hst
    have hinc := hinterval s t hst
    have hmass :=
      congrArg ENNReal.toReal
        (avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
          X ω s t)
    rw [← hmass] at hinc
    exact hinc
  · intro τ u hu n hstop hinterior
    have h := hstrip τ u hu n hstop hinterior
    rw [← hRQ] at h
    exact h
