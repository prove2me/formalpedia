-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_unit_value_regular_minimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:54:52.662521+00:00
-- url     : https://prove2.me/submissions/e958d71d-e375-41e5-b40e-39f02c101a56

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_discounted_value_dominates_drift_at_threshold
import Theorems.Thm_AvramDividend_Classical_vcstar_near_field_jump_nonpos_of_unit_value
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
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
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hunit : 1 ≤ vcstar W x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ z : ℝ, 0 < z →
          deriv W (cstar W).toReal ≤ deriv W z) :=
    Or.inr ⟨hbarrier, hminimal⟩
  have hderiv :=
    vcstar_deriv_ge_one_of_regular_minimal W hreg hpositive hmin
  have hdiff : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      DifferentiableAt ℝ (vcstar W) z := by
    intro z hz
    exact (hderiv z hz.1).1
  have hder : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      1 ≤ deriv (vcstar W) z := by
    intro z hz
    exact (hderiv z hz.1).2
  have hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal :=
    left_affine_majorant_of_deriv_ge_one
      (vcstar W) (cstar W).toReal (le_of_lt hbarrier)
      (vcstar_continuousOn_Icc_below_positive_cstar
        X q W hW hbarrier) hdiff hder
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW hbarrier
  have hvalue : X.c ≤ q * vcstar W x :=
    vcstar_discounted_value_dominates_drift_at_threshold
      X q hq W hW hbarrier x hx hthreshold
  obtain ⟨hint, hres⟩ :=
    vcstar_near_field_jump_nonpos_of_unit_value
      X q W hW hmono hchord x hx hunit hvalue
  have hright : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  refine ⟨hint, ?_⟩
  rw [hright]
  simpa using (max_eq_right hres :
    max (X.generator (vcstar W) x - q * vcstar W x) 0 = 0)
