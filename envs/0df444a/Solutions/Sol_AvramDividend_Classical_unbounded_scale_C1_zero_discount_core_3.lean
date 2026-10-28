-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:11:05.301918+00:00
-- url     : https://prove2.me/submissions/2f3e6d2a-206f-4ff2-82ec-a1de8fbdfcc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_absolute_continuity
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_zero_iff_positive_discount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hW : IsScaleFunction X 0 W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hq : (0 : ℝ) < 1 := one_pos
  obtain ⟨Wq, hWq⟩ :=
    unbounded_positive_discount_scale_exists_from_zero X hnbv W hW 1 hq
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv 1 hq
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * Wq x
  have hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * Wq x :=
    fun x _ => rfl
  have hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    unbounded_tilted_scale_absolute_continuity X 1 hq Wq hWq hnbv φ hφ hroot V hV
  have hWqC1 : ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) :=
    esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one φ Wq V hVdiff hV
  have hiff : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) ↔
      ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) :=
    unbounded_scale_C1_zero_iff_positive_discount X hnbv W hW 1 hq Wq hWq
  exact hiff.mpr hWqC1
