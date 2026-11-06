-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:17:41.145207+00:00
-- url     : https://prove2.me/submissions/774726fe-cf44-4986-8c07-108c3863c72e

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopping time selects a predictable left-grid cell, so its
conditional mean-zero martingale increment still has zero unconditional mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    ∀ i, (∫ ω, if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0 ∂P)
      = 0 := by
  intro i
  let S : Set Ω := {ω : Ω | (u i : WithTop ℝ≥0) < τ ω}
  have hPred : MeasurableSet[𝓕.rightCont (u i)] S :=
    avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
      X τ hStop u i
  letI : IsProbabilityMeasure P := X.isProbability
  have hm : 𝓕.rightCont (u i) ≤ mΩ := (𝓕.rightCont).le (u i)
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hMeas : MeasurableSet S := hm _ hPred
  have hCondRestrict :
      ∀ᵐ ω ∂P.restrict S,
        condExp (𝓕.rightCont (u i)) P (M i) ω = 0 :=
    ae_restrict_of_ae (hCondZero i)
  have hSetIntegral :=
    setIntegral_condExp hm (hMI i) hPred
  have hMean : (∫ ω in S, M i ω ∂P) = 0 := by
    calc
      (∫ ω in S, M i ω ∂P) =
          (∫ ω in S, condExp (𝓕.rightCont (u i)) P (M i) ω ∂P) :=
        hSetIntegral.symm
      _ = 0 := by
        rw [integral_congr_ae hCondRestrict]
        simp
  have hMask : (fun ω : Ω =>
      if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) =
      S.indicator (M i) := by
    funext ω
    by_cases h : ω ∈ S
    · have ht : (u i : WithTop ℝ≥0) < τ ω := h
      simp only [if_pos ht, Set.indicator_of_mem h]
    · have ht : ¬ (u i : WithTop ℝ≥0) < τ ω := h
      simp only [if_neg ht, Set.indicator_of_notMem h]
  rw [hMask, integral_indicator hMeas]
  exact hMean
