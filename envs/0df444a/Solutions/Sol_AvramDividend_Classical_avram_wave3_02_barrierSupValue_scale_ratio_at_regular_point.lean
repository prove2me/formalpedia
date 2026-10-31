-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_at_regular_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:53:15.697992+00:00
-- url     : https://prove2.me/submissions/9df68006-e88d-44ee-a479-ddb69e48ef10

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Genuine reflected Stieltjes reward equals the local scale-ratio
whenever the original scale function has a nonzero derivative at the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hLo := barrierSupValue_stopped_renewal_lower_bound
    X hX q hq W hW a ha hD hd
  have hHi := barrierSupValue_stopped_renewal_upper_bound
    X hX q hq W hW a ha hD hd
  exact barrierSupValue_of_stopped_renewal_bounds
    X hX q hq W hW a ha hD hd hLo hHi
