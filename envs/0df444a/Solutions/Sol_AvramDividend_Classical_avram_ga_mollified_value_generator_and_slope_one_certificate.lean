-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_mollified_value_generator_and_slope_one_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:46:51.4632+00:00
-- url     : https://prove2.me/submissions/dea692af-f427-4e44-ab4a-98cd2e41f86f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_positive_one_sided_smoothing_preserves_secant
import Theorems.Thm_AvramDividend_Classical_avram_ga_smooth_secant_implies_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_upperstrip_convolution_bound
open MeasureTheory Filter Set AvramDividend.Classical
noncomputable section

theorem solution
    (μ : Measure ℝ) (φ V g : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b c : ℝ) (hc : 0 ≤ c)
    (hSec : ∀ x y : ℝ, x ≤ y → y - x ≤ V y - V x)
    (hg : ∀ u, g u ≤ if b < u then c else 0)
    (hVI : ∀ y, Integrable (fun z => φ z * V (y - ε*z)) μ)
    (hgI : ∀ y, Integrable (fun z => φ z * g (y - ε*z)) μ)
    (y : ℝ)
    (hDiff : DifferentiableAt ℝ
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y) :
    1 ≤ deriv (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ∧
      (∫ z, φ z * g (y - ε*z) ∂μ) ≤
        if b < y then c else 0 := by
  have hConvSec :
      ∀ a d : ℝ, a ≤ d →
        d - a ≤ (∫ z, φ z * V (d - ε*z) ∂μ) -
          (∫ z, φ z * V (a - ε*z) ∂μ) := by
    intro a d had
    exact avram_ga_positive_one_sided_smoothing_preserves_secant
      μ φ V hφI hφpos hφnorm hSec ε a d had (hVI a) (hVI d)
  constructor
  · exact avram_ga_smooth_secant_implies_deriv_ge_one
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) hConvSec y hDiff
  · exact avram_ga_one_sided_upperstrip_convolution_bound
      μ φ g hφI hφpos hφnorm hPositive ε hε b y c hc hg (hgI y)
