-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:09:24.737983+00:00
-- url     : https://prove2.me/submissions/ed5f80b5-1256-405b-a9af-92f70953bdb1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Generator jump-integrability of the q-scale function below `c*`, in the branch
where the barrier candidate is explicitly `C^2` and the barrier normalisation
factor is non-zero.

`ContDiffOn ℝ 2 (vcstar W)` on the barrier interval together with the non-zero
normalisation factor give `ContDiffOn ℝ 2 W` on the same interval, because
`vcstar W` is the barrier value `divE (W z) (scaleDeriv W (cstar W).toReal)`
below the cap, so `W` is a non-zero constant multiple of `vcstar W` there.
Second-order regularity of the scale function gives the integrable compensated
jump term of the Levy generator.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x := by
  have hW2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
    scaleFunction_contDiffOn_two_of_vcstar_nonzero W hvc hk
  intro x hx
  exact scaleFunction_generatorIntegrable_of_contDiff_two
    X q W hW (cstar W).toReal x hx hW2
