-- Prove2me | solution 5 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:51:10.609005+00:00
-- url     : https://prove2.me/submissions/0614fdec-9024-4a9b-aa6a-481b3bf7eafa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_regular_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

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
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hregular (hcase : 0 < X.σ ∨ X.BoundedVariation) :
      deriv (vcstar W) (cstar W).toReal = 1 := by
    have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
      scaleFunction_contDiff_one X hX q hq W hW
    have hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
      scaleDeriv_pos X hX q hq W hW
    have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
      hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
    have hmin : (cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x →
            deriv W (cstar W).toReal ≤ deriv W x) :=
      cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont
    exact vcstar_deriv_one_of_regular_minimal W ha hreg hpos hmin
  rcases h_smooth with hσ | hbv | hC2
  · exact hregular (Or.inl hσ)
  · exact hregular (Or.inr hbv)
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hC2
