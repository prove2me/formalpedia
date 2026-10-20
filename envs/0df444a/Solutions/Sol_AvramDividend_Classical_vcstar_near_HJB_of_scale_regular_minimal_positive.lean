-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_scale_regular_minimal_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:21:37.204564+00:00
-- url     : https://prove2.me/submissions/eed6e963-c9c0-472b-9d24-76e8c6ee8659

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_regular_deriv_minimum
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (hbarrier : 0 < (cstar W).toReal)
    (hminimal : ∀ z : ℝ, 0 < z →
      deriv W (cstar W).toReal ≤ deriv W z)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  exact vcstar_near_HJB_of_regular_deriv_minimum
    X q hq W hW hreg hpositive
    (cstar W).toReal rfl hbarrier hminimal
    (vcstar_continuousOn_Icc_below_positive_cstar
      X q W hW hbarrier)
    x hx hx1 hthreshold
