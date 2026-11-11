-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_levy_X_time_mean_triplet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:30:57.225722+00:00
-- url     : https://prove2.me/submissions/0da61b19-19aa-4784-ba91-d0f1141a02b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_laplace_quotient_to_mean
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_laplace_quotient_to_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Identify the first moment from two independently verified right derivatives
of the original exponential moment, using uniqueness of real limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, X.X t ω ∂P) =
        (t : ℝ) * (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν)) := by
  intro t
  have hAnalytic :=
    avram_ja18g_original_levy_X_laplace_quotient_to_mean
      X hX hFinite t
  have hTriplet :=
    avram_ja18g_original_levy_X_laplace_quotient_to_triplet
      X hX hFinite t
  exact tendsto_nhds_unique hAnalytic hTriplet
