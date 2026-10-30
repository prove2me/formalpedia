-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_value_of_root_smooth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:12:04.813588+00:00
-- url     : https://prove2.me/submissions/fc32dfbd-7e19-4914-9b14-a219c7ae1c5a

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_deriv_pos_of_root_smooth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual all-capital reflected value under precisely the root smoothness alternatives. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hx
  let a : ℝ := (cstar W).toReal
  change dividendValue X q x (barrierStrategy X x a) =
    ENNReal.ofReal (barrierValue W a x)
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  by_cases hzero : a = 0
  · simpa [hzero] using
      (barrier_strategy_value_zero_all_capital X hX q hq W hW x hx)
  · have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
    have hcpos : 0 < cstar W := (ENNReal.toReal_pos_iff.mp ha).1
    have hd : 0 < deriv W a :=
      avram_wave3_02_cstar_deriv_pos_of_root_smooth
        X hX q hq W hW hc hcpos h_smooth
    exact avram_wave3_02_all_capital_of_local_deriv_nonzero
      X hX q hq W hW a ha (ne_of_gt hd) x hx
