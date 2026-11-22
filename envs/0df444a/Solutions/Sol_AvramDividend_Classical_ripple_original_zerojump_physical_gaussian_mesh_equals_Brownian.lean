-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_physical_gaussian_mesh_equals_Brownian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:20:38.171088+00:00
-- url     : https://prove2.me/submissions/e8fadf8c-09c4-4f53-86fd-70ea716b3143

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (G : ℕ → Ω → ℝ) (N : ℕ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      (∀ (i : ℕ) (ω : Ω),
        X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c =
          X.σ * (W.W ((s i + Δ : ℝ≥0) : ℝ) ω -
            W.W (s i : ℝ) ω)) ∧
      (∀ ω : Ω,
        (Finset.range N).sum (fun i =>
          G i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
            (Δ : ℝ) * X.c)) =
        (Finset.range N).sum (fun i =>
          (X.σ * G i ω) *
            (W.W ((s i + Δ : ℝ≥0) : ℝ) ω -
              W.W (s i : ℝ) ω))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hσpos : 0 < X.σ :=
    avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν
  have hσne : X.σ ≠ 0 := ne_of_gt hσpos
  obtain ⟨W, hW⟩ :=
    avram_lsc_zerojump_original_sameSpace_brownian X hν hσpos
  have hCell (i : ℕ) (ω : Ω) :
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c =
        X.σ * (W.W ((s i + Δ : ℝ≥0) : ℝ) ω -
          W.W (s i : ℝ) ω) := by
    have hRight : W.W ((s i + Δ : ℝ≥0) : ℝ) ω =
        (X.X (s i + Δ) ω - ((s i + Δ : ℝ≥0) : ℝ) * X.c)
          / X.σ := by
      simpa using hW ((s i + Δ : ℝ≥0) : ℝ) ω
    have hLeft : W.W (s i : ℝ) ω =
        (X.X (s i) ω - (s i : ℝ) * X.c) / X.σ := by
      simpa using hW (s i : ℝ) ω
    rw [hRight, hLeft]
    field_simp
    push_cast
    ring
  refine ⟨W, hCell, ?_⟩
  intro ω
  apply Finset.sum_congr rfl
  intro i hi
  rw [hCell i ω]
  ring
