-- Prove2me | solution 7 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:55:14.534649+00:00
-- url     : https://prove2.me/submissions/30dd8aaa-deac-4814-8d5f-e600f87d7143
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hlt : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ := hbv.2
    rw [hvar] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨φ, hφ, hroot⟩ :=
    AvramDividend.Classical.positive_esscher_root_of_unbounded_variation X hnbv q hq
  classical
  set V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x with hVdef
  have hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x := by
    intro x _
    rfl
  have hVdiff : ContDiffOn ℝ 1 V (Ioi 0) :=
    AvramDividend.Classical.esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hvar φ hφ hroot V hV
  exact AvramDividend.Classical.esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
    φ W V hVdiff hV
