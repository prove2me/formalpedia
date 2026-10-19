-- Prove2me | solution 1 for AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:19:57.848388+00:00
-- url     : https://prove2.me/submissions/da686c4b-6891-4b76-84ed-c1a969489d9e

import Mathlib
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {G : Filtration ℕ mΩ}
    (Y M : ℕ → Ω → ℝ) (hY : Adapted G Y)
    (hM : Martingale M G P) (a : ℝ) (m : ℕ) :
    (∫ ω, M (hittingBtwn Y (Set.Ioi a) 0 m ω) ω ∂P) =
      ∫ ω, M 0 ω ∂P := by
  set τ : Ω → WithTop ℕ := fun ω => ((hittingBtwn Y (Set.Ioi a) 0 m ω : ℕ) : WithTop ℕ) with hτdef
  have hτ : IsStoppingTime G τ := hY.isStoppingTime_hittingBtwn measurableSet_Ioi
  have h0 : IsStoppingTime G (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) := isStoppingTime_const G 0
  have hle : (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) ≤ τ := fun ω => by
    simp only [hτdef]; exact_mod_cast Nat.zero_le _
  have hbdd : ∀ ω, τ ω ≤ m := fun ω => by
    simp only [hτdef]; exact_mod_cast hittingBtwn_le (u := Y) (s := Set.Ioi a) (n := 0) ω
  have h1 := hM.submartingale.expected_stoppedValue_mono h0 hτ hle hbdd
  have h2 := hM.neg.submartingale.expected_stoppedValue_mono h0 hτ hle hbdd
  have e1 : stoppedValue M τ = fun ω => M (hittingBtwn Y (Set.Ioi a) 0 m ω) ω := by
    funext ω; rfl
  have e0 : stoppedValue M (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) = M 0 := by
    funext ω; rfl
  have e2 : stoppedValue (-M) τ = fun ω => -(M (hittingBtwn Y (Set.Ioi a) 0 m ω) ω) := by
    funext ω; rfl
  have e3 : stoppedValue (-M) (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) = fun ω => -(M 0 ω) := by
    funext ω; rfl
  rw [e1, e0] at h1
  rw [e2, e3, integral_neg, integral_neg] at h2
  linarith

