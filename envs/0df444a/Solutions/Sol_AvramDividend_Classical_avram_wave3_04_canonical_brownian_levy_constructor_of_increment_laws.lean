-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:38:52.880814+00:00
-- url     : https://prove2.me/submissions/f8f24ad3-e3c2-4de9-9cef-7ceb7134f1c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_cadlag_no_positive_jumps
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_levy_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
open LevyStochCalc.Brownian

/-- Assemble a genuine Gaussian Lévy process from its Brownian law,
path regularity, and the two independent-increment interfaces. -/
theorem solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
    (hadapt : Adapted 𝓕
      (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)))
    (hindep : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω : ℝ≥0 → ℝ =>
          (brownian t ω - brownian 0 ω - (t : ℝ)) -
          (brownian s ω - brownian 0 ω - (s : ℝ))) inferInstance)
        (𝓕 s) gaussianLimit)
    (hstationary : ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib
        (fun ω : ℝ≥0 → ℝ =>
          (brownian t ω - brownian 0 ω - (t : ℝ)) -
          (brownian s ω - brownian 0 ω - (s : ℝ)))
        (fun ω : ℝ≥0 → ℝ =>
          brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
        gaussianLimit gaussianLimit) :
    ∃ X : SpectrallyNegativeLevy gaussianLimit 𝓕,
      X.X = (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)) ∧
      X.c = -1 ∧ X.σ = 1 ∧ X.ν = 0 := by
  classical
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun t ω => brownian t ω - brownian 0 ω - (t : ℝ)
  obtain ⟨W, hW⟩ := canonical_brownian_realTime_bridge
  refine ⟨{
    X := B
    c := -1
    σ := 1
    ν := 0
    isProbability := inferInstance
    σ_nonneg := by norm_num
    ν_Ici := by simp
    ν_integrable := by simp
    X_zero := by
      intro ω
      simp [B]
    rightCont := by
      intro ω t
      exact (canonical_drifted_brownian_cadlag_no_positive_jumps ω).1 t
    leftLim := by
      intro ω t ht
      exact (canonical_drifted_brownian_cadlag_no_positive_jumps ω).2.1 t ht
    noPosJumps := by
      intro ω t l ht hlim
      exact (canonical_drifted_brownian_cadlag_no_positive_jumps ω).2.2 t l ht hlim
    adapted := hadapt
    indepIncrements := hindep
    stationaryIncrements := hstationary
    laplace := by
      intro t θ hθ
      have hB (ω : ℝ≥0 → ℝ) :
          B t ω = W.W (t : ℝ) ω - (t : ℝ) := by
        simp only [B, hW t ω]
      simpa only [hB] using W.drift_minus_one_levy_laplace t θ
  }, rfl, rfl, rfl, rfl⟩
