-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:30:45.971372+00:00
-- url     : https://prove2.me/submissions/0fbc61ca-7b51-4d21-b8a7-313149a4ea11

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- True killed reflected-regulator valuation under canonical smooth Lévy regimes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hPos : 0 < deriv W a :=
    avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
      X hX q hq W hW hbranch a ha
  have hNe : deriv W a ≠ 0 := ne_of_gt hPos
  have hD : HasDerivAt W (deriv W a) a :=
    hasDerivAt_of_deriv_ne_zero hNe
  have hLo :=
    barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hD hNe
  have hHi :=
    barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hD hNe
  exact barrierSupValue_of_stopped_renewal_bounds
    X hX q hq W hW a ha hD hNe hLo hHi
