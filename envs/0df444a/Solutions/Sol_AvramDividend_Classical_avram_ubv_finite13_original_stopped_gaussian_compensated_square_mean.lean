-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_compensated_square_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:18:40.706175+00:00
-- url     : https://prove2.me/submissions/47098a5f-71bc-4af5-bd80-1b1f0703c6cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The compensated-square Gaussian source has the same expectation at two
ordered bounded stopping indices on a common physical-time grid. -/
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
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω)^2 - (t : ℝ) * X.σ^2
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) α ω ∂P) =
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) β ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω => (M t ω)^2 - (t : ℝ) * X.σ^2
  change (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) α ω ∂P) =
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) β ω ∂P)
  have hSample :=
    (avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded).2
  calc
    (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) α ω ∂P) =
      (∫ ω, P[stoppedValue (fun i : ℕ => Q (grid i)) β |
          hα.measurableSpace] ω ∂P) := integral_congr_ae hSample
    _ = (∫ ω, stoppedValue (fun i : ℕ => Q (grid i)) β ω ∂P) :=
      integral_condExp hα.measurableSpace_le
