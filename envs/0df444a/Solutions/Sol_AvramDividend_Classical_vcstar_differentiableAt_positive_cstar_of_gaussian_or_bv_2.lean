-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:44:45.348557+00:00
-- url     : https://prove2.me/submissions/6cd1d4f4-13c2-41cc-baa4-19894c0cabeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Data.ENNReal.Real
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
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
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
  have hglobal := vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  exact (hglobal _ ha).1
