-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T18:37:02.57028+00:00
-- url     : https://prove2.me/submissions/bee1e1e8-ac5c-478b-9457-573d31069136
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_unbounded_variation

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

The unbounded-variation C1 regularity theorem is the openly published
sibling `scaleFunction_contDiff_one_of_unbounded_variation`, whose sole
hypothesis beyond the scale function is exactly `not X.BoundedVariation`.
It is used here as a sketch dependency, so this source is a source-faithful
reduction: it is not a complete proof of the parent while that child
remains Open.
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
  exact scaleFunction_contDiff_one_of_unbounded_variation X q W hW hnbv
