-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:17:40.167198+00:00
-- url     : https://prove2.me/submissions/4892d995-0a29-4ccd-9afb-f52fe902b068

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Revalidated HJB42 against current Prove2Me checker after old candidate admission became stale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε L M K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2)) :
    Integrable (fun z : ℝ =>
      if -(ε / 2) ≤ z then L * |z| else 2 * M)
      (X.ν.restrict (Iio (0 : ℝ))) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hBase : Integrable (fun z : ℝ => min (ε / 2) (-z)) μ :=
    avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
      X hBV (ε / 2) (by positivity) (by linarith)
  have hBig : Integrable (fun z : ℝ => K * min (ε / 2) (-z)) μ :=
    hBase.const_mul K
  have hMeas : AEStronglyMeasurable
      (fun z : ℝ => if -(ε / 2) ≤ z then L * |z| else 2 * M) μ :=
    (Measurable.ite measurableSet_Ici
      (measurable_const.mul measurable_id.abs)
      measurable_const).aestronglyMeasurable
  have hDom : ∀ᵐ z ∂μ,
      ‖(if -(ε / 2) ≤ z then L * |z| else 2 * M)‖ ≤
        K * min (ε / 2) (-z) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    change z < 0 at hz
    have hn : 0 ≤ (if -(ε / 2) ≤ z then L * |z| else 2 * M) := by
      split_ifs <;> positivity
    have hk : 0 ≤ K * min (ε / 2) (-z) :=
      mul_nonneg hK (le_min (by positivity) (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    by_cases hs : -(ε / 2) ≤ z
    · have hm : min (ε / 2) (-z) = -z :=
        min_eq_right (by linarith)
      simpa only [if_pos hs, abs_of_neg hz, hm] using
        (mul_le_mul_of_nonneg_right hKL (by linarith : 0 ≤ -z))
    · have hm : min (ε / 2) (-z) = ε / 2 :=
        min_eq_left (by linarith)
      simpa only [if_neg hs, hm] using hKM
  exact hBig.mono' hMeas hDom
