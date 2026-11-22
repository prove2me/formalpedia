-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_full_GH_mesh_equals_Brownian_chaos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:24:29.719799+00:00
-- url     : https://prove2.me/submissions/0026ddd2-c1dc-4e11-bc88-aafe1b6bbfbd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_physical_gaussian_mesh_equals_Brownian
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (G H : ℕ → Ω → ℝ) (N : ℕ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ ω : Ω,
        (Finset.range N).sum (fun i =>
          let Z : ℝ := X.X (s i + Δ) ω - X.X (s i) ω -
            (Δ : ℝ) * X.c
          G i ω * Z + H i ω * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2)) =
        (Finset.range N).sum (fun i =>
          let ZW : ℝ := W.W ((s i + Δ : ℝ≥0) : ℝ) ω -
            W.W (s i : ℝ) ω
          (X.σ * G i ω) * ZW +
            (X.σ ^ 2 * H i ω) * (ZW ^ 2 - (Δ : ℝ))) := by
  classical
  obtain ⟨W, hCell, _⟩ :=
    ripple_original_zerojump_physical_gaussian_mesh_equals_Brownian
      X hBV hν s Δ G N
  refine ⟨W, ?_⟩
  intro ω
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [hCell i ω]
  ring
