-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_distribution_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:48:10.400575+00:00
-- url     : https://prove2.me/submissions/4c3c2927-7600-4183-9a4e-f08494901d17

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ x : ℝ, ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by
  obtain ⟨S, hS⟩ :=
    chat04_esscher_infinite_survival_stieltjes_measure X θ hθ
  have hSneg : ∀ y : ℝ, y < 0 → S y = 0 := by
    intro y hy
    rw [hS y, chat04_esscher_infimum_survival_zero_negative_reserve X θ y hy]
    simp
  have hFbound : ∀ y : ℝ, (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) ≤ 1 := by
    intro y
    calc
      (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) ≤ ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X 0 ω - (0 : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) :=
        iInf_le _ (0 : ℝ≥0)
      _ ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal
          (esscher_weighted_lower_survival_mass_unit_interval X θ hθ y 0).2
  have hSbound : ∀ y : ℝ, S y ≤ 1 := by
    intro y
    rw [hS y]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hFbound y)
  letI : IsFiniteMeasure S.measure :=
    stieltjes_isFiniteMeasure_of_zero_negative_bounded_one S hSneg hSbound
  refine ⟨S.measure, inferInstance, ?_⟩
  intro x
  rw [stieltjes_measure_Iic_of_zero_negative S hSneg x, hS x]
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hFbound x))
