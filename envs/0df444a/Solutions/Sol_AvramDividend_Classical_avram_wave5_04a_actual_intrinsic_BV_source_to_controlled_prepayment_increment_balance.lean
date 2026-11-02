-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:16:07.451294+00:00
-- url     : https://prove2.me/submissions/e0284059-fca5-45c5-b07b-c79e42473669

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The source part of every actual controlled reserve increment is the
original intrinsic negative left-jump measure plus its downward BV residual.
The chronological right dividend payment is a *separate* algebraic update,
not a jump of the original source; no Ito--Meyer theorem is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
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
        riskProcess X x D t ω - riskProcess X x D s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s) - (D t ω - D s ω)) ∧
      (∀ t : ℝ≥0,
        riskProcess X x D t ω - (rightLimit D t ω - D t ω) =
          x + X.X t ω - rightLimit D t ω) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hsource⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_, ?_⟩
  · intro s t hst
    have hinc := hsource s t hst
    dsimp [riskProcess]
    linarith only [hinc]
  · intro t
    simp only [riskProcess]
    ring
