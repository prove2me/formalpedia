-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_diffuse_signed_norm_le_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:46:26.394553+00:00
-- url     : https://prove2.me/submissions/9ca0c382-598c-4298-b942-7d48869bb37d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A single compact-band coefficient controls all original stopped
diffuse dividend remainders by the corresponding true Cash path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes σ ∩ Iic (T : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)‖ ≤
        (1 + K) *
          ((∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
              Real.exp (-(q * (T : ℝ)))) := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hwC2 a b hab hBand
  refine ⟨K, hK0, ?_⟩
  intro ω
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hsubset : S ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  have hmass : (ν ω) S < ⊤ := by
    calc
      (ν ω) S ≤ (dividendMeasure D ω) S := hdom ω S
      _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hkernel :=
    avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
      X x D hD σ T ν q hq w a b K hK0 hK hstate ω
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae hmass hkernel
  calc
    _ ≤ (1 + K) * (ν ω).real S := hnorm
    _ ≤ (1 + K) *
        ((∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal /
           Real.exp (-(q * (T : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
          D hD ω σ T (ν ω) (hdom ω) q hq) (by linarith)
