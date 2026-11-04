-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:11:59.922024+00:00
-- url     : https://prove2.me/submissions/f0a9e7da-6e00-4726-a07f-28401b2a930b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- Compact local Lipschitzness automatically supplies the original-source
nonlinear small-negative-jump measurability and BV first-moment domination. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + 1) b) :
    IntegrableOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-1 : ℝ) 0) X.ν := by
  have hmap : MapsTo (fun z : ℝ => u + z)
      (Ioo (-1 : ℝ) 0) (Icc a b) := by
    intro z hz
    rcases hu with ⟨hlo, hhi⟩
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨by linarith, by linarith⟩
  have hcont : ContinuousOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-1 : ℝ) 0) := by
    have hcomp : ContinuousOn (fun z : ℝ => w (u + z))
        (Ioo (-1 : ℝ) 0) :=
      hLip.continuousOn.comp
        ((continuous_const.add continuous_id).continuousOn) hmap
    exact hcomp.sub continuousOn_const
  have hMeas : AEStronglyMeasurable
      (fun z : ℝ => w (u + z) - w u)
      (X.ν.restrict (Ioo (-1 : ℝ) 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  exact avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
    X hBV w K a b u hLip hu hMeas
