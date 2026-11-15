-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:20:33.267307+00:00
-- url     : https://prove2.me/submissions/f915a777-4ce7-4fdd-aeac-632f8b93891d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω)
        (Ici t) t := by
  obtain ⟨J0, hJ0, hRight0, hZero0⟩ :=
    AvramDividend.Classical.avram_ja18e_original_smallband_locally_uniform_cadlag_limit
      X hX hFinite
  filter_upwards [hJsource, hJ0, hRight0] with ω hJω hJ0ω hRightω
  have hAll (u : ℝ≥0) : Jsmall u ω = J0 u ω :=
    tendsto_nhds_unique (hJω u) (hJ0ω u)
  have heq : (fun u : ℝ≥0 => Jsmall u ω) =
      (fun u : ℝ≥0 => J0 u ω) := by
    funext u
    exact hAll u
  intro t
  rw [heq]
  exact hRightω t
