-- Prove2me | solution 1 for AvramDividend.Classical.levy_integrable_at_natural_horizon_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:55:58.688053+00:00
-- url     : https://prove2.me/submissions/19c09c16-2a33-4578-b12b-059983df48ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (n : ℕ) : Integrable (X.X (n : ℝ≥0)) P := by
  haveI := X.isProbability
  induction n with
  | zero =>
    have : X.X ((0 : ℕ) : ℝ≥0) = fun _ => 0 := by funext ω; simpa using X.X_zero ω
    rw [this]; exact integrable_const _
  | succ n ih =>
    have hle : ((n : ℕ) : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_succ n
    have hid := X.stationaryIncrements _ _ hle
    have hsub : ((n + 1 : ℕ) : ℝ≥0) - ((n : ℕ) : ℝ≥0) = 1 := by
      push_cast; exact add_tsub_cancel_left _ _
    rw [hsub] at hid
    have hinc : Integrable (fun ω => X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X ((n : ℕ) : ℝ≥0) ω) P :=
      hid.integrable_iff.mpr hX.2.1
    have := hinc.add ih
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
