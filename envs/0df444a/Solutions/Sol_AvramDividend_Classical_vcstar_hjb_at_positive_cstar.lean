-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:46:02.475985+00:00
-- url     : https://prove2.me/submissions/2ad95732-794d-40e5-b696-31fdfd498941
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      max (X.generator (vcstar W) (cstar W).toReal -
           q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  have hGenerator :=
    vcstar_generator_eq_zero_at_positive_cstar X hX q hq W hW
      hc hcpos h_smooth hgen
  have hDerivative :=
    vcstar_deriv_eq_one_at_positive_cstar X hX q hq W hW
      hc hcpos h_smooth
  refine ⟨hGenerator.1, ?_⟩
  simp [hGenerator.2, hDerivative]
