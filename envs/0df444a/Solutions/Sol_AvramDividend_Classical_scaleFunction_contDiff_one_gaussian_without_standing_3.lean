-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:47:37.599608+00:00
-- url     : https://prove2.me/submissions/fe9f7184-7079-489b-ae0b-cc862f63c921

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  have hVc : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    esscher_tilted_scale_C1_of_positive_gaussian_without_standing
      X q hq W hW hσ φ hφ hroot V hV
  exact esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
    φ W V hVc hV
