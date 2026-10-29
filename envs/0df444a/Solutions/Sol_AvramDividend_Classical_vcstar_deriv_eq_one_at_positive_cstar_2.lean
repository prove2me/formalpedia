-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:36:27.105296+00:00
-- url     : https://prove2.me/submissions/0bc61145-bc40-4d9b-8119-cbd273174a7c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
import Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hdiff : DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
    rcases h_smooth with hσ | hBV | hCtwo
    · exact vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos (Or.inl hσ)
    · exact vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos (Or.inr hBV)
    · have hwithin : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) :=
        hCtwo.differentiableOn (by norm_num)
      have hmem : (cstar W).toReal ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
      exact (hwithin _ hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)
  change deriv (barrierValue W (cstar W).toReal) (cstar W).toReal = 1
  exact barrierValue_deriv_one_of_differentiableAt
    W (cstar W).toReal (le_of_lt ha) hdiff
