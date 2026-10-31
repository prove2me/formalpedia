-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:04:22.344984+00:00
-- url     : https://prove2.me/submissions/276cfe55-2521-4db7-87c5-86c5868a0edc

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_two_sided_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- The actual killed reflected-regulator reward has the exact q-scale ratio
at each differentiability point of the original scale, without global C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hdiff : DifferentiableAt ℝ W a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hdpos : 0 < deriv W a :=
    avram_wave3_02_deriv_pos_of_pointwise_diff X hX q hq W hW a ha hdiff
  have hsand :=
    avram_wave3_02_standing_two_sided_sandwich X hX q hq W hW a ha
  have hlo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q :=
    hsand.mono (fun ε hε => hε.1)
  have hhi : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) :=
    hsand.mono (fun ε hε => hε.2)
  exact barrierSupValue_of_stopped_renewal_bounds
    X hX q hq W hW a ha hdiff.hasDerivAt (ne_of_gt hdpos) hlo hhi
