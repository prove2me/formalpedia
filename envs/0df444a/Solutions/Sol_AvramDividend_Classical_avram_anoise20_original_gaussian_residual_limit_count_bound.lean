-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise20_original_gaussian_residual_limit_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:32:18.818108+00:00
-- url     : https://prove2.me/submissions/caa4b7e2-9d88-448b-9ffc-330ccb01d11c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Original-residual cutoff error survives the physical same-path limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (ω : Ω)
    (hRsource : Tendsto
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
      atTop (nhds (R T ω)))
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    |R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (1 / ((n : ℝ) + 1)) * (N.toReal + A) := by
  intro N A
  have hConverges :
      Tendsto
        (fun m : ℕ =>
          |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω|)
        atTop
        (nhds |R T ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω|) := by
    exact (hRsource.sub tendsto_const_nhds).abs
  have hBoundEventually :
      ∀ᶠ m : ℕ in atTop,
        |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
        (1 / ((n : ℝ) + 1)) * (N.toReal + A) := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    simpa only [N, A] using
      avram_anoise19_original_gaussian_residual_cutoff_count_bound
        X hFinite n m hnm T ω hNfin
  exact le_of_tendsto hConverges hBoundEventually