-- Prove2me | solution 5 for AvramDividend.Classical.vcstar_deriv_ge_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:44:56.185991+00:00
-- url     : https://prove2.me/submissions/f8f4ddd5-f91b-4cfb-8efe-754b79a21d3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal

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
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x) :=
    cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont
  exact vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin
