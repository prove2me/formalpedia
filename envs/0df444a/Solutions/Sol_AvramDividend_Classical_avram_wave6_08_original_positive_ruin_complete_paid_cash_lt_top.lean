-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:19:24.734658+00:00
-- url     : https://prove2.me/submissions/c35e4099-d485-402f-8796-e26f66d50e82

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The entire actual positive-ruin stopped dividend reward is finite,
including the initial right payment and excluding the ruin right payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hleft :
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤ :=
    avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
      D hD ω q hq τ hτ
  have hzero :
      (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤ := by
    have hsingleton :
        (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
          μ ({(0 : ℝ)} : Set ℝ) := by simp
    rw [hsingleton]
    have hsubset : ({(0 : ℝ)} : Set ℝ) ⊆ Icc (0 : ℝ) (τ : ℝ) := by
      intro t ht
      simp only [mem_singleton_iff] at ht
      subst t
      exact ⟨le_refl _, NNReal.coe_nonneg τ⟩
    have hbound : μ ({(0 : ℝ)} : Set ℝ) ≤ μ (Icc (0 : ℝ) (τ : ℝ)) :=
      measure_mono hsubset
    rw [avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
      D hD ω τ] at hbound
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  calc
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) +
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) :=
          avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
            D hD ω q τ hτ
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hzero, hleft⟩
