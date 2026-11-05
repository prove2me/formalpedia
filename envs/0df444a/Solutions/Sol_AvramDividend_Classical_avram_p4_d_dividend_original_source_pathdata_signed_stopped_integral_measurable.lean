-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_source_pathdata_signed_stopped_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:17:10.409807+00:00
-- url     : https://prove2.me/submissions/607089a7-e836-4f6a-8219-4c45973c185f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_joint_stop_window_measurable_sections
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original source component measurability and a single jointly measurable
pre-ruin closed-horizon window suffice for measurability of the stopped
dividend-gradient integral against a genuine s-finite dividend kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (κdiff : Kernel Ω ℝ) [IsSFiniteKernel κdiff]
    (hXL : Measurable (fun p : Ω × ℝ =>
      Function.leftLim (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal))
    (hDR : Measurable (fun p : Ω × ℝ =>
      rightLimit D p.2.toNNReal p.1))
    (hDeriv : Measurable (deriv w))
    (hWindowJoint : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) := by
  have hSections :=
    avram_p4_d_dividend_original_joint_stop_window_measurable_sections
      σ τ hWindowJoint
  have hJoint :=
    avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
      X x D hD σ τ q w hXL hDR hDeriv hWindowJoint
  exact avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
    X x D hD σ τ q w κdiff hSections hJoint
