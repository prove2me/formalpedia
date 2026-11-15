-- Prove2me | solution 1 for AvramDividend.Classical.avram_b85_original_finiteactivity_jumpfree_smallmark_limiting_exact_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:16:22.777912+00:00
-- url     : https://prove2.me/submissions/3ddf9910-b70a-48cd-ba0d-389e337c8b5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b82_original_jumpfree_limit_small_compensation_drift
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original finite-activity source, a true jumpfree interval carries the exact full negative-small-mark compensation drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ ω (u : ℝ≥0), s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by
  have hMoment :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hNeg : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    hMoment.neg
  exact avram_b82_original_jumpfree_limit_small_compensation_drift
    X Jsmall hJlim (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))
    hNeg s t hOrder hNoJump
