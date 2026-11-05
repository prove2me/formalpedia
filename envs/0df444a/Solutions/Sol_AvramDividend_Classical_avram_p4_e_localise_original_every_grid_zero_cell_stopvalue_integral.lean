-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_every_grid_zero_cell_stopvalue_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:01:58.60425+00:00
-- url     : https://prove2.me/submissions/e15f233a-9075-4a62-b183-e794f7b215bb

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original true process has a centred zero-clock stoppedValue on every varying grid when it starts at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ)
    (e : ℕ → ℕ → ℝ≥0)
    (hZeroGrid : ∀ k, e k 0 = 0)
    (hZeroProcess : ∀ ω, f 0 ω = 0) :
    ∀ k, (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) = 0 := by
  intro k
  have hPoint : (fun ω : Ω => stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω) = (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    calc
      stoppedValue (fun i : ℕ => f (e k i))
          (fun _ : Ω => (0 : WithTop ℕ)) ω =
        f (e k 0) ω :=
          avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
            X f (e k) (fun _ : Ω => 0) ω
      _ = 0 := by
        rw [hZeroGrid k]
        exact hZeroProcess ω
  rw [hPoint]
  simp
