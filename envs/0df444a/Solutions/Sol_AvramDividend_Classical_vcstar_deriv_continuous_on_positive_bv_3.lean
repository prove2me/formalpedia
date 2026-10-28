-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_deriv_continuous_on_positive_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:40:09.882924+00:00
-- url     : https://prove2.me/submissions/96fd6428-10ec-4816-8359-69beeffd79f6

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global BV C1 regularity gives continuity of the ordinary derivative
on the positive reserve axis, including the canonical barrier join. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContinuousOn (deriv (vcstar W)) (Ioi 0) := by
  have hC1 : ContDiffOn ℝ 1 (vcstar W) (Ioi 0) :=
    vcstar_global_C1_bv_positive_barrier X hX q hq W hW hc hcpos hbv
  exact hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
