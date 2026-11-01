-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_source_large_negative_test_increment_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:19:40.208277+00:00
-- url     : https://prove2.me/submissions/2ca5782f-a20f-4bc4-b16b-8a7814931218

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The original source test-function jump increment is square integrable over
large negative marks without any first absolute Lévy jump moment.
On a nonnegative bounded reserve band, negative overshoots use w=0.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (y : ℝ) (hy : 0 ≤ y)
    (hGen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => (w (y + z) - w y) ^ 2)
      (Iic (-1 : ℝ)) X.ν := by
  have hcont : ContinuousOn w (Icc (0 : ℝ) y) :=
    hw_cont.mono (by intro z hz; exact hz.1)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) y)).exists_bound_of_continuousOn hcont
  have hMy : ‖w y‖ ≤ M := hM y ⟨hy, le_refl y⟩
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) hMy
  have hbound (z : ℝ) (hz : z ∈ Iic (-1 : ℝ)) :
      ‖w (y + z) - w y‖ ≤ 2 * M := by
    have hyz : y + z ≤ y := by
      have : z ≤ -1 := hz
      linarith
    have hleft : ‖w (y + z)‖ ≤ M := by
      by_cases hn : y + z < 0
      · rw [hw_neg (y + z) hn]
        simpa using hMnonneg
      · exact hM (y + z) ⟨le_of_not_gt hn, hyz⟩
    calc
      ‖w (y + z) - w y‖ ≤ ‖w (y + z)‖ + ‖w y‖ :=
        norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  have hL1 :
      IntegrableOn (fun z : ℝ => w (y + z) - w y) (Iic (-1 : ℝ)) X.ν :=
    generatorIntegrand_large_negative_integrable X w y hGen
  have hAE :
      AEStronglyMeasurable (fun z : ℝ => (w (y + z) - w y) ^ 2)
        (X.ν.restrict (Iic (-1 : ℝ))) :=
    hL1.aestronglyMeasurable.pow 2
  refine IntegrableOn.of_bound
    (levy_negative_mass_away_from_zero_finite X 1 (by norm_num))
    hAE ((2 * M) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := X.ν)
    (s := Iic (-1 : ℝ)) measurableSet_Iic] with z hz
  have hb := hbound z hz
  calc
    ‖(w (y + z) - w y) ^ 2‖ =
        ‖w (y + z) - w y‖ ^ 2 := norm_pow _ _
    _ ≤ (2 * M) ^ 2 := by gcongr
