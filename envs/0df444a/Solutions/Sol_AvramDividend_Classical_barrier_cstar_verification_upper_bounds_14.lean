-- Prove2me | solution 14 for AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:48:46.362144+00:00
-- url     : https://prove2.me/submissions/880b35cf-1c08-44c6-b6c1-94ced71b0f7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_capped_upper_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_upper_bound_of_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Assemble the two original-process verification inequalities. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
  constructor
  · exact vcstar_capped_upper_bound_all_capital
      X hX q hq W hW hc h_smooth
  · intro hgen
    exact vcstar_unrestricted_upper_bound_of_generator
      X hX q hq W hW hc h_smooth hgen
