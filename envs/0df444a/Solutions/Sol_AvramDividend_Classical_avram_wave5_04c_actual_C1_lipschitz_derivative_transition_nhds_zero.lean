-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_lipschitz_derivative_transition_nhds_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:06.978316+00:00
-- url     : https://prove2.me/submissions/0b71efb9-9c5c-4fee-a2b8-af72b1d851ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_strong_continuity_at_zero_bounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) :
    Tendsto (fun t : ℝ≥0 => ∫ ω, deriv w (x + X.X t ω) ∂P)
      (nhds 0) (nhds (deriv w x)) := by
  have hcont : Continuous (deriv w) := hwC1.continuous_deriv (by norm_num)
  have hLip' : LipschitzWith (Real.toNNReal L) w := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa [Real.dist_eq, Real.coe_toNNReal, hL] using hLip u v
  have hBound (y : ℝ) : ‖deriv w y‖ ≤ L := by
    simpa only [Real.coe_toNNReal, hL] using
      (norm_deriv_le_of_lipschitz (x₀ := y) hLip')
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro τ hτ
  change Tendsto (fun n : ℕ => ∫ ω, deriv w (x + X.X (τ n) ω) ∂P)
    atTop (nhds (deriv w x))
  exact levy_transition_strong_continuity_at_zero_bounded
    X (deriv w) hcont L hBound x τ hτ