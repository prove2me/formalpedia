-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:09:14.971708+00:00
-- url     : https://prove2.me/submissions/97d1ca5f-848a-40ec-8678-33bba9c8a79b
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

/-- Infinite small-jump variation gives C1 q-scale-function regularity
without first-moment standing assumptions.

The infinite absolute first moment of the Levy measure on `Ioo (-1) 0`
forces the spectrally negative process to have unbounded variation: the
pinned definition reads `BoundedVariation L := L.sigma = 0 /\
  (integral ENNReal.ofReal |y| over Ioo (-1) 0 < top)`, so bounded variation
would give a finite small-jump first moment, contradicting `hvar`.

The unbounded-variation C1 conclusion then follows from the published
Esscher excursion representation
`unbounded_esscher_excursion_integrated_scale_representation`, which holds
under `not X.BoundedVariation` alone with no standing assumption, together
with two Proved analytic theorems: `excursion_integral_scale_derivative`
turns the integrated exponential representation into the pointwise
derivative identity, and `contDiffOn_one_of_deriv_eq_continuous_product_Ioi`
turns that identity, with a continuous logarithmic-derivative coefficient,
into `ContDiffOn ℝ 1 W (Ioi 0)`.

The excursion representation is used here as a sketch dependency, so this
source is a source-faithful reduction: it is not a complete proof of the
parent while that child remains Open.
-/
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
