-- Prove2me | solution 8 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:20:14.715987+00:00
-- url     : https://prove2.me/submissions/65b22c41-d6f4-462e-8a46-80cb796e671c
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
    intro hBV
    have hlt : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ := hBV.2
    rw [hvar] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨φ, hφ, hroot⟩ :=
    AvramDividend.Classical.positive_esscher_root_of_unbounded_variation
      X hnbv q hq
  have hVdiff : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) :=
    AvramDividend.Classical.esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hvar φ hφ hroot
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (fun x _ => rfl)
  exact AvramDividend.Classical.esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
    φ W (fun x : ℝ => Real.exp (-(φ * x)) * W x)
    hVdiff (fun x _ => rfl)
