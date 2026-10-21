-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:49:24.743199+00:00
-- url     : https://prove2.me/submissions/c824290a-6f8a-45bf-8dc6-60c239ae4105
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_absolute_continuity
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_deriv_eq_continuous_product_Ioi

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
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) < ⊤ := hbv.2
    rw [hvar] at hsmall
    exact lt_irrefl _ hsmall
  obtain ⟨φ, μ, hφ, hnull, hfin, hμcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    excursion_integral_scale_derivative W φ μ hμcont hexp
  have hconst : ContinuousOn (fun _ : ℝ => φ) (Ioi 0) :=
    continuous_const.continuousOn
  have hg : ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) :=
    hconst.add hμcont
  have hderiv' : ∀ x : ℝ, 0 < x →
      HasDerivAt W ((φ + μ.real (Ici x)) * W x) x := by
    intro x hx
    have hx' := hderiv x hx
    have hcomm : W x * (φ + μ.real (Ici x)) = (φ + μ.real (Ici x)) * W x :=
      mul_comm _ _
    rw [hcomm] at hx'
    exact hx'
  exact contDiffOn_one_of_deriv_eq_continuous_product_Ioi W
    (fun x : ℝ => φ + μ.real (Ici x)) hg hderiv'
