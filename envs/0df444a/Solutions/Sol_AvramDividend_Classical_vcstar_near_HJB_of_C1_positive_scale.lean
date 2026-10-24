-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_C1_positive_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:50:14.378719+00:00
-- url     : https://prove2.me/submissions/5ef4f75e-c654-4820-9893-bbb27b45d218

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_scale_regular_minimal_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive-axis C1 regularity forces canonical barrier minimality,
    allowing the exact near-field HJB theorem to apply. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hderpos : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (hbarrier : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hmin := cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont
  rcases hmin with hzero | ⟨_, hminimal⟩
  · exact False.elim ((ne_of_gt hbarrier) hzero)
  · exact vcstar_near_HJB_of_scale_regular_minimal_positive
      X q hq W hW hC1 hderpos hbarrier hminimal
      x hx hx1 hthreshold
