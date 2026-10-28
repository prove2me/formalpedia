-- Prove2me | solution 6 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:07:25.231136+00:00
-- url     : https://prove2.me/submissions/bbb29998-b113-46fe-8d05-896578430846
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_of_scaledW_harmonic
import Theorems.Thm_AvramDividend_Classical_scaled_scaleFunction_q_harmonic_below_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by
  have hscaled : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable
          (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x ∧
        X.generator
            (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x -
          q * divE (W x) (scaleDeriv W (cstar W).toReal) = 0 :=
    scaled_scaleFunction_q_harmonic_below_cstar X hX q hq W hW h_smooth hc
  exact generator_vcstar_eq_zero_of_scaledW_harmonic X hX q hq W hW h_smooth hc hscaled
