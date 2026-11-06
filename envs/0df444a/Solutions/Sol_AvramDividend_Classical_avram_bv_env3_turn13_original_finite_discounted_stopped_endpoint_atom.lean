-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:10:37.838615+00:00
-- url     : https://prove2.me/submissions/17c77c5f-e700-450a-8d04-a1a5fa7a697b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (τ T : ℝ≥0) (hτT : τ ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ ({(τ : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) < ⊤ := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ ({(τ : ℝ)} : Set ℝ)
  have hs : MeasurableSet s :=
    (paymentTimes_measurable σ).inter (measurableSet_singleton (τ : ℝ))
  have hsubset : s ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    have hu0 : 0 ≤ u :=
      (paymentTimes_membership_to_nNReal_active σ u hu.1).1
    have hEq : u = (τ : ℝ) := Set.mem_singleton_iff.mp hu.2
    refine ⟨hu0, ?_⟩
    rw [hEq]
    exact_mod_cast hτT
  have hweight : ∀ u ∈ s,
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ 1 := by
    intro u hu
    have hu0 : 0 ≤ u :=
      (paymentTimes_membership_to_nNReal_active σ u hu.1).1
    have hreal : Real.exp (-(q * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq hu0])
    calc
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 1 := by norm_num
  have hint : (∫⁻ u in s, ENNReal.ofReal (Real.exp (-(q * u))) ∂μ) ≤ μ s := by
    calc
      (∫⁻ u in s, ENNReal.ofReal (Real.exp (-(q * u))) ∂μ) ≤
          (∫⁻ u in s, (1 : ℝ≥0∞) ∂μ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with u hu
        exact hweight u hu
      _ = μ s := by simp
  have hmass : μ s < ⊤ := by
    calc
      μ s ≤ μ (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact lt_of_le_of_lt hint hmass
