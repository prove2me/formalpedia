-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_ge_one_of_scale_C1_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:43:07.22222+00:00
-- url     : https://prove2.me/submissions/f97ba964-30f4-4ecc-98ae-a336dc18b62c

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  have hpositive : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  have hderivpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos_of_tilted_positive_monotone X hX q hq W hW
      hpositive hdiff htilt
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧ ∀ x : ℝ, 0 < x →
        deriv W (cstar W).toReal ≤ deriv W x) :=
    cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont
  intro x hx
  exact vcstar_deriv_ge_one_of_regular_minimal W hreg hderivpos hmin x hx
