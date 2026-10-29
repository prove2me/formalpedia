-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:13:06.303528+00:00
-- url     : https://prove2.me/submissions/f4439583-ce4a-4dd7-b041-e3c5af9808b2

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn
import Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  rcases h_smooth with hgaussian | hbv | htwo
  · have ha : 0 < (cstar W).toReal :=
      ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
    have hdiff : DifferentiableAt ℝ (vcstar W) (cstar W).toReal :=
      vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos (Or.inl hgaussian)
    change deriv (barrierValue W (cstar W).toReal) (cstar W).toReal = 1
    exact barrierValue_deriv_one_of_differentiableAt
      W (cstar W).toReal (le_of_lt ha) hdiff
  · have ha : 0 < (cstar W).toReal :=
      ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
    have hdiff : DifferentiableAt ℝ (vcstar W) (cstar W).toReal :=
      vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos (Or.inr hbv)
    change deriv (barrierValue W (cstar W).toReal) (cstar W).toReal = 1
    exact barrierValue_deriv_one_of_differentiableAt
      W (cstar W).toReal (le_of_lt ha) hdiff
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos htwo
