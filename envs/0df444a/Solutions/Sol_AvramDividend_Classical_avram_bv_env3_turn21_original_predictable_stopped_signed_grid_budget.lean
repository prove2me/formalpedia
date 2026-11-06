-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:01:16.39842+00:00
-- url     : https://prove2.me/submissions/7d6b477f-8db5-4e20-99b3-e96cf2043351

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn10_original_selected_signed_grid_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-process predictable conditional means and negative drift control a stopped finite-grid signed source. -/
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
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hMean : ∀ i < m,
      (∫ ω, (if i < k ω then M i ω else 0) ∂P) = 0 := by
    intro i hi
    have hm : (𝓕.rightCont (u i)) ≤ mΩ := (𝓕.rightCont).le (u i)
    haveI : SigmaFinite (P.trim hm) := inferInstance
    have hRestr : ∀ᵐ ω ∂P.restrict {ω : Ω | i < k ω},
        condExp (𝓕.rightCont (u i)) P (M i) ω = 0 :=
      ae_restrict_of_ae (hCondZero i)
    have hs : MeasurableSet {ω : Ω | i < k ω} :=
      measurableSet_lt measurable_const hk
    have hMask : (fun ω : Ω => if i < k ω then M i ω else 0) =
        ({ω : Ω | i < k ω}.indicator (M i)) := by
      funext ω
      by_cases h : i < k ω <;> simp [Set.indicator_apply, h]
    calc
      (∫ ω, (if i < k ω then M i ω else 0) ∂P) =
          (∫ ω in {ω : Ω | i < k ω}, M i ω ∂P) := by
        rw [hMask]
        exact integral_indicator hs
      _ = (∫ ω in {ω : Ω | i < k ω},
          condExp (𝓕.rightCont (u i)) P (M i) ω ∂P) :=
        (setIntegral_condExp hm (hMI i) (hPredictable i)).symm
      _ = 0 := by
        rw [integral_congr_ae hRestr]
        simp
  exact avram_bv_env3_turn10_original_selected_signed_grid_budget
    P m k hk hkBound M B hMI hBI hMean hDrift
