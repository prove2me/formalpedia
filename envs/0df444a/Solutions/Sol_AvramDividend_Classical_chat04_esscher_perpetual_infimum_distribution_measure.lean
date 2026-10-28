-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_perpetual_infimum_distribution_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:44:00.832602+00:00
-- url     : https://prove2.me/submissions/dc9176cc-7dd3-470b-ae38-3439a01f8451

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
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
    ∃ ν : Measure ℝ, ∀ x : ℝ, ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by
  obtain ⟨S, hS⟩ :=
    chat04_esscher_infinite_survival_stieltjes_measure X θ hθ
  have hSneg : ∀ y : ℝ, y < 0 → S y = 0 := by
    intro y hy
    rw [hS y, chat04_esscher_infimum_survival_zero_negative_reserve X θ y hy]
    simp
  refine ⟨S.measure, ?_⟩
  intro x
  rw [stieltjes_measure_Iic_of_zero_negative S hSneg x, hS x]
  have hle : (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) ≤ 1 := by
    calc
      (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) ≤ ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X 0 ω - (0 : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) :=
        iInf_le _ (0 : ℝ≥0)
      _ ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal
          (esscher_weighted_lower_survival_mass_unit_interval X θ hθ x 0).2
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
