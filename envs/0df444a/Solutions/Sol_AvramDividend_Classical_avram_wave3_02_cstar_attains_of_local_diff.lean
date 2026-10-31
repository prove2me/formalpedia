-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_attains_of_local_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:39:51.847516+00:00
-- url     : https://prove2.me/submissions/42d917ba-8895-4018-a9d9-a96a7d8ae416

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_all_capital_of_local_diff
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital_of_value_formula
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual reflected cstar policy is cap-admissible and attains vcstar
at all nonnegative capitals under pointwise scale differentiability at cstar. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hlocal : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
  exact barrier_cstar_attains_value_all_capital_of_value_formula
    X hX q hq W hW hc
    (avram_wave3_02_cstar_all_capital_of_local_diff
      X hX q hq W hW hc hlocal)
