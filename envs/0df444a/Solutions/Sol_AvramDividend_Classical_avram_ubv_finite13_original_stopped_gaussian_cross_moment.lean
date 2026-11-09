-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_cross_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:00:07.751942+00:00
-- url     : https://prove2.me/submissions/491245ef-e4e2-42af-a4b5-2a12e6811171

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The early and late sampled stopped Gaussian values have cross moment
equal to the early stopped value's second moment, on the original space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hBound : ∀ ω, β ω ≤ (N : WithTop ℕ))
    (A B : Ω → ℝ)
    (hA : A = stoppedValue
      (fun i : ℕ => fun ω => X.X (grid i) ω - (grid i : ℝ) * X.c) α)
    (hB : B = stoppedValue
      (fun i : ℕ => fun ω => X.X (grid i) ω - (grid i : ℝ) * X.c) β)
    (hAadapt : StronglyMeasurable[hα.measurableSpace] A)
    (hBI : Integrable B P)
    (hCrossI : Integrable (fun ω => A ω * B ω) P) :
    (∫ ω, A ω * B ω ∂P) = (∫ ω, A ω * A ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSample :=
    (avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hBound).1
  have hCE : A =ᵐ[P] P[B | hα.measurableSpace] := by
    simpa only [hA, hB] using hSample
  have hPull : P[(fun ω => A ω * B ω) | hα.measurableSpace] =ᵐ[P]
      (fun ω => A ω * P[B | hα.measurableSpace] ω) := by
    exact condExp_mul_of_stronglyMeasurable_left hAadapt hCrossI hBI
  calc
    (∫ ω, A ω * B ω ∂P) =
        (∫ ω, P[(fun ω => A ω * B ω) | hα.measurableSpace] ω ∂P) := by
      symm
      exact integral_condExp hα.measurableSpace_le
    _ = (∫ ω, A ω * P[B | hα.measurableSpace] ω ∂P) :=
      integral_congr_ae hPull
    _ = (∫ ω, A ω * A ω ∂P) := by
      apply integral_congr_ae
      filter_upwards [hCE] with ω hω
      exact congrArg (fun z : ℝ => A ω * z) hω.symm
