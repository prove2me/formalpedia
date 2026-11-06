-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:52:04.747297+00:00
-- url     : https://prove2.me/submissions/9d98a3db-1a5a-4d7b-9599-e3117ef51b68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Conditional mean zero survives a predictable stopped physical-grid selection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (k : Ω → ℕ)
    (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hPredictable : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    ∀ i, (∫ ω in {ω : Ω | i < k ω}, M i ω ∂P) = 0 := by
  intro i
  letI : IsProbabilityMeasure P := X.isProbability
  have hm : (𝓕.rightCont (u i)) ≤ mΩ := (𝓕.rightCont).le (u i)
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hCondRestrict :
      ∀ᵐ ω ∂P.restrict {ω : Ω | i < k ω},
        condExp (𝓕.rightCont (u i)) P (M i) ω = 0 :=
    ae_restrict_of_ae (hCondZero i)
  have hSetIntegral :=
    setIntegral_condExp hm (hMI i) (hPredictable i)
  calc
    (∫ ω in {ω : Ω | i < k ω}, M i ω ∂P) =
      (∫ ω in {ω : Ω | i < k ω},
        condExp (𝓕.rightCont (u i)) P (M i) ω ∂P) :=
      hSetIntegral.symm
    _ = 0 := by
      rw [integral_congr_ae hCondRestrict]
      simp
