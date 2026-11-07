-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_zero_discount_scale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:16:22.300552+00:00
-- url     : https://prove2.me/submissions/12ff1cb8-402a-4db3-b2c8-8e74f1f97ebf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_scale_inverse_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ W₀ : ℝ → ℝ, IsScaleFunction X 0 W₀ := by
  obtain ⟨W₀, hSupp, hNonneg, hCont, hLap⟩ :=
    avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse X hX hσ
  have hMono : MonotoneOn W₀ (Ici (0 : ℝ)) :=
    avram_p4_f6_gaussian_zero_scale_inverse_monotone
      X hX hσ W₀ hSupp hNonneg hCont hLap
  refine ⟨W₀, hSupp, hNonneg, hCont, hMono, ?_⟩
  intro θ hθ hψ
  simpa only [sub_zero] using hLap θ hθ hψ
