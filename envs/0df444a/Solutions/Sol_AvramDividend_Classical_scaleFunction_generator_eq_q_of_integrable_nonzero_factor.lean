-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_integrable_nonzero_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:10:30.17184+00:00
-- url     : https://prove2.me/submissions/5b77320a-31e1-4381-ba57-61ae3fa86f2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hint : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
  intro x hx
  have ha : 0 < (cstar W).toReal := lt_trans hx.1 hx.2
  rcases h_smooth with hσ | hbv | hvc
  · exact
      (scaleFunction_generator_eq_zero
        X hX q hq W hW (cstar W).toReal ha
        (Or.inl hσ) x hx).2
  · exact
      (scaleFunction_generator_eq_zero
        X hX q hq W hW (cstar W).toReal ha
        (Or.inr (Or.inl hbv)) x hx).2
  · have hC2 :=
      scaleFunction_contDiff_two_below_cstar_of_vcstar W hvc hk
    exact
      (scaleFunction_generator_eq_zero
        X hX q hq W hW (cstar W).toReal ha
        (Or.inr (Or.inr hC2)) x hx).2
