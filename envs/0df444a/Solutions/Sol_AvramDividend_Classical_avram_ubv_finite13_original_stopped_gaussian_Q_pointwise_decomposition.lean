-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:22:14.681573+00:00
-- url     : https://prove2.me/submissions/7ff5edcf-f061-496c-bcb3-0f2b86341d17

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- A stopped compensated square decomposes into the original stopped square
and the original sample-time quadratic-variation bracket. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (τ : Ω → WithTop ℕ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2
    stoppedValue (fun i : ℕ => Q (grid i)) τ =
      (fun ω => stoppedValue (fun i : ℕ => M (grid i)) τ ω ^ 2 -
        stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
          τ ω) := by
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2
  let U : ℕ → Ω → ℝ := fun i ω => M (grid i) ω ^ 2
  let V : ℕ → Ω → ℝ := fun i _ => (grid i : ℝ) * X.σ ^ 2
  change stoppedValue (U - V) τ =
    (fun ω => stoppedValue (fun i : ℕ => M (grid i)) τ ω ^ 2 -
      stoppedValue V τ ω)
  have hU : stoppedValue U τ =
      (fun ω => stoppedValue (fun i : ℕ => M (grid i)) τ ω ^ 2) := by
    simpa only [U] using
      (stoppedValue_comp (u := fun i : ℕ => M (grid i)) (τ := τ)
        (fun z : ℝ => z ^ 2))
  calc
    stoppedValue (U - V) τ = stoppedValue U τ - stoppedValue V τ :=
      stoppedValue_sub
    _ = (fun ω => stoppedValue (fun i : ℕ => M (grid i)) τ ω ^ 2 -
          stoppedValue V τ ω) := by
      rw [hU]
      rfl
