-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_scale_strictMonoOn_positive_pure_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:42:38.803426+00:00
-- url     : https://prove2.me/submissions/d68f44cd-a8b3-4e9f-80b2-bdec975acef0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The positive ordinary derivative supplied by genuine first records
makes the q-scale function strictly increasing on every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    StrictMonoOn W (Ioi (0 : ℝ)) := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_infinite_variation_without_standing
      X q hq W hW hvar
  have hpos : ∀ a : ℝ, 0 < a → 0 < deriv W a :=
    avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing
      X q hq W hW hvar
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
    hC1.continuousOn
  intro a ha
  have ha' : 0 < a := by
    have hm : a ∈ Ioi (0 : ℝ) := by
      simpa only [interior_Ioi] using ha
    change (0 : ℝ) < a at hm
    exact hm
  exact hpos a ha'
