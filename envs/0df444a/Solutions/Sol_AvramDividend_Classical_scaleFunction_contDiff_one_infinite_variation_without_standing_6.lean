-- Prove2me | solution 6 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T04:56:04.757919+00:00
-- url     : https://prove2.me/submissions/3962bb30-3396-4268-9c71-9c1b441f52cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hBV
    have hlt : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ := hBV.2
    rw [hvar] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨phi0, mu0, hphi0, hnull0, hfin0, hcont0, hexp0⟩ :=
    AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (phi0 + mu0.real (Ici x))) x :=
    AvramDividend.Classical.excursion_integral_scale_derivative
      W phi0 mu0 hcont0 hexp0
  have hderiv' : ∀ x : ℝ, 0 < x →
      HasDerivAt W ((phi0 + mu0.real (Ici x)) * W x) x := by
    intro x hx
    simpa [mul_comm] using hderiv x hx
  have hg : ContinuousOn (fun t : ℝ => phi0 + mu0.real (Ici t)) (Ioi 0) :=
    continuousOn_const.add hcont0
  exact AvramDividend.Classical.contDiffOn_one_of_deriv_eq_continuous_product_Ioi
    W (fun t : ℝ => phi0 + mu0.real (Ici t)) hg hderiv'
