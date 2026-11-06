-- Prove2me | solution 13 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:25:56.999726+00:00
-- url     : https://prove2.me/submissions/ef365d1a-0d2a-438a-89dd-97de26a20f20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_upper_bound_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_root_optimality_of_original_verification_pair

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source-exact root from the capped and unrestricted original verification consumers. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x =
            ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧
            X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hUpper :
      (∀ x : ℝ, 0 ≤ x →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
    constructor
    · exact barrier_cstar_capped_value_upper_bound
        X hX q hq W hW hc h_smooth
    · intro hgen
      exact vcstar_unrestricted_upper_bound_of_generator
        X hX q hq W hW hc h_smooth hgen
  exact avram_sweep16_root_optimality_of_original_verification_pair
    X hX q hq W hW hUpper
