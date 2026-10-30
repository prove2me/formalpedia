-- Prove2me | solution 8 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:20:19.877711+00:00
-- url     : https://prove2.me/submissions/1235132f-95dc-4ee4-8949-a815ac3c23e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine killed reflected-regulator reward equals the scale derivative ratio. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hPos : 0 < deriv W a := scaleDeriv_pos X hX q hq W hW a ha
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
