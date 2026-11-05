-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:46.279284+00:00
-- url     : https://prove2.me/submissions/ce0b9cea-e351-4a0a-bede-5280adf65fe6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_real_jordan_parts
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

/-- Signed compact-test measure equality from positive extended moments. -/
theorem solution
    (μ ν : Measure ℝ)
    (hInt : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      Integrable f μ ∧ Integrable f ν)
    (hPos : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
        (∫⁻ x, ENNReal.ofReal (f x) ∂ν))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    (∫ x, g x ∂μ) = (∫ x, g x ∂ν) := by
  obtain ⟨gp, gn, hgp, hcp, hsp, hgn, hcn, hsn, hparts⟩ :=
    avram_p2_a_zero_rate_compact_negative_real_jordan_parts
      g hg hc hneg
  have hgp0 : ∀ x : ℝ, 0 ≤ gp x := fun x => (hparts x).1
  have hgn0 : ∀ x : ℝ, 0 ≤ gn x := fun x => (hparts x).2.1
  obtain ⟨hgpμ, hgpν⟩ := hInt gp hgp hcp hsp hgp0
  obtain ⟨hgnμ, hgnν⟩ := hInt gn hgn hcn hsn hgn0
  have hEqp : (∫ x, gp x ∂μ) = (∫ x, gp x ∂ν) :=
    avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
      μ ν gp hgp0 hgpμ hgpν (hPos gp hgp hcp hsp hgp0)
  have hEqn : (∫ x, gn x ∂μ) = (∫ x, gn x ∂ν) :=
    avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
      μ ν gn hgn0 hgnμ hgnν (hPos gn hgn hcn hsn hgn0)
  have hdecomp : g = fun x => gp x - gn x :=
    funext (fun x => (hparts x).2.2)
  calc
    (∫ x, g x ∂μ) =
        (∫ x, gp x - gn x ∂μ) := by rw [hdecomp]
    _ = (∫ x, gp x ∂μ) - (∫ x, gn x ∂μ) :=
      integral_sub hgpμ hgnμ
    _ = (∫ x, gp x ∂ν) - (∫ x, gn x ∂ν) := by rw [hEqp, hEqn]
    _ = (∫ x, gp x - gn x ∂ν) := (integral_sub hgpν hgnν).symm
    _ = (∫ x, g x ∂ν) := by rw [hdecomp]
