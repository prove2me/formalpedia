-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:02:25.819765+00:00
-- url     : https://prove2.me/submissions/af1e8d7c-acab-4ab2-9bdc-25fe02e0895a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn10_original_selected_signed_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Predictability and zero conditional means give a nonpositive signed stopped-grid budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hPredictable : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), (M i ω + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω), (M i ω + B i ω) ∂P) ≤ 0 := by
  apply avram_bv_env3_turn10_original_selected_signed_grid_budget
    P m k hk hkBound M B hMI hBI _ hDrift
  intro i hi
  rw [avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
    P k hk i (M i)]
  exact avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
    X u k M hMI hPredictable hCondZero i
