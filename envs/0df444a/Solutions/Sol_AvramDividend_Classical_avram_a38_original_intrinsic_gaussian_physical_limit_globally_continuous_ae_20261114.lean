-- Prove2me | solution 1 for AvramDividend.Classical.avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:18:20.798248+00:00
-- url     : https://prove2.me/submissions/a9e44604-a868-462b-9e17-7f18b4800887

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => R t ω) := by
  have hCompact :=
    avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
      X hFinite R hR
  filter_upwards [hCompact] with ω hω
  exact avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
    (fun t => R t ω) hω
