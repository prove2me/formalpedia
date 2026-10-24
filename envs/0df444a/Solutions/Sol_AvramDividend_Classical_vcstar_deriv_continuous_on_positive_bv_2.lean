-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_deriv_continuous_on_positive_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:09:06.203218+00:00
-- url     : https://prove2.me/submissions/d4aad40e-9aef-49b2-8ca4-803fee98f7d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_C1_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- BV derivative continuity follows from the remaining stochastic C1
    regularity input and Proved deterministic derivative pasting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContinuousOn (deriv (vcstar W)) (Ioi 0) := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  obtain ⟨hpositive, htilt⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hderivpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos_of_tilted_positive_monotone
      X hX q hq W hW hpositive hdiff htilt
  exact vcstar_deriv_continuous_C1_positive
    W ha hreg (hderivpos _ ha)
