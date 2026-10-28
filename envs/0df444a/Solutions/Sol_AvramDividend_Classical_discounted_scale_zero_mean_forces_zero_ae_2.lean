-- Prove2me | solution 2 for AvramDividend.Classical.discounted_scale_zero_mean_forces_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:09:14.653013+00:00
-- url     : https://prove2.me/submissions/19bd3dce-d1ed-42e0-8bc4-84560d21e729

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- An integrable nonnegative discounted scale reward with zero mean must
vanish at each fixed time, since the exponential discount is positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, W (X.X t ω) = 0 := by
  have hW_nonneg (z : ℝ) : 0 ≤ W z := by
    by_cases hz : z < 0
    · rw [hW.1 z hz]
    · exact hW.2.1 z (le_of_not_gt hz)
  have hReward : 0 ≤ᵐ[P]
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) :=
    Filter.Eventually.of_forall (fun ω =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (hW_nonneg _))
  have hZero : (fun ω : Ω =>
      Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hReward hInt).mp
      (by simpa only [hW0] using hMean)
  filter_upwards [hZero] with ω hω
  exact (mul_eq_zero.mp hω).resolve_left (ne_of_gt (Real.exp_pos _))
