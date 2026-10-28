-- Prove2me | solution 1 for AvramDividend.Classical.generator_vcstar_eq_zero_of_scaledW_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:55:25.523161+00:00
-- url     : https://prove2.me/submissions/acbd0d82-7fc8-4d57-8953-d1428ff52d7c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hscaled : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable
          (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x ∧
        X.generator
            (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x -
          q * divE (W x) (scaleDeriv W (cstar W).toReal) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by
  intro x hx
  have hxa : x < (cstar W).toReal := (Set.mem_Ioo.mp hx).2
  have hscale := hscaled x hx
  have hagree : ∀ z : ℝ, z < (cstar W).toReal →
      vcstar W z = divE (W z) (scaleDeriv W (cstar W).toReal) := by
    intro z hz
    exact vcstar_eq_scaledW_le_cstar_of_support W hW.1 z (le_of_lt hz)
  have heq := generator_eq_of_agree_below X (vcstar W)
    (fun z => divE (W z) (scaleDeriv W (cstar W).toReal))
    (cstar W).toReal x hxa hagree
  constructor
  · exact heq.1.mpr hscale.1
  · rw [heq.2, vcstar_eq_scaledW_le_cstar_of_support W hW.1 x (le_of_lt hxa)]
    exact hscale.2
