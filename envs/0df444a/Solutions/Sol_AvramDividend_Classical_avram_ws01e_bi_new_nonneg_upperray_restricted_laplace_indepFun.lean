-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:08:55.89462+00:00
-- url     : https://prove2.me/submissions/9b731782-d0c0-41e3-8268-ba249de48769

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Nonnegative supremum makes negative upper rays automatic for all-beta tests. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hRnonneg : ∀ ω, 0 ≤ R ω) (hDnonneg : ∀ ω, 0 ≤ D ω)
    (hFactor : ∀ a β : ℝ, 0 ≤ a → 0 < β →
      (∫⁻ ω in R ⁻¹' Set.Ioi a,
          ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) =
        P (R ⁻¹' Set.Ioi a) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P)) :
    IndepFun R D P := by
  apply AvramDividend.Classical.avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
    P R D hR hD hDnonneg
  intro a β hβ
  by_cases ha : 0 ≤ a
  · exact hFactor a β ha hβ
  · have haneg : a < 0 := lt_of_not_ge ha
    have hA : R ⁻¹' Set.Ioi a = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le haneg (hRnonneg ω)
    simp [hA]
