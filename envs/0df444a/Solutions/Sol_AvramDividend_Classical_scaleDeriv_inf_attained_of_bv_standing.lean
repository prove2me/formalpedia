-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_inf_attained_of_bv_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:31:38.376302+00:00
-- url     : https://prove2.me/submissions/ade0d0ff-ad9d-4d4a-bda3-11a6fe95986b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have htop : Tendsto (deriv W) atTop atTop :=
    bv_scaleDeriv_tendsto_atTop_of_C1 X hX q hq W hW hbv hdiff
  simpa only [derivZeroPlus] using
    (positive_minimum_or_right_liminf_of_tendsto_atTop
      (deriv W) hcont htop)
