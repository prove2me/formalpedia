-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_source_measure_and_discounted_stopped_C1_real_limit_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:11.902994+00:00
-- url     : https://prove2.me/submissions/ab06ce0f-9eac-41a4-a498-9113a7da9292

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Single original BV source sample event for the true intrinsic
negative-mark measure decomposition and the nonpositive limit of
any convergent stopped discounted C1 residual partition sums. -/
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
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV,
      avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos
      X hBV x D hD w C hw_grad q] with ω hsource hlimsign
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  obtain ⟨Q, hQdef, hQmono, hQlimit⟩ := hlimsign
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
  · intro τ u hu n hstop hinterior L hlim
    have h := hQlimit τ u hu n hstop hinterior L
    apply h
    simpa only [← hRQ] using hlim
