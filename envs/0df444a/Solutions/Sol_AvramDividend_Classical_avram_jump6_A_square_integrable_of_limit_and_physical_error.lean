-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_square_integrable_of_limit_and_physical_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:32:51.669022+00:00
-- url     : https://prove2.me/submissions/2c0b7e5c-5639-4284-b504-6d25c4a091df

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
/-- The physical approximation has L2 norm bounded by the intrinsic limit and its error. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R G : Ω → ℝ)
    (hRSq : Integrable (fun ω => (R ω) ^ 2) P)
    (hErr : Integrable (fun ω => (R ω - G ω) ^ 2) P)
    (hGmeas : AEStronglyMeasurable G P) :
    Integrable (fun ω => (G ω) ^ 2) P := by
  let E : Ω → ℝ := fun ω => R ω - G ω
  have hErr' : Integrable (fun ω => E ω ^ 2) P := by
    simpa only [E] using hErr
  have hDom : Integrable (fun ω => 2 * ((R ω) ^ 2 + (E ω) ^ 2)) P :=
    (hRSq.add hErr').const_mul 2
  apply hDom.mono (hGmeas.pow 2)
  filter_upwards [] with ω
  have hEq : G ω = R ω - E ω := by dsimp [E]; ring
  have hSq : (G ω) ^ 2 ≤ 2 * ((R ω) ^ 2 + (E ω) ^ 2) := by
    rw [hEq]
    nlinarith [sq_nonneg (R ω + E ω)]
  have hLeft : 0 ≤ (G ω) ^ 2 := sq_nonneg _
  have hRight : 0 ≤ 2 * ((R ω) ^ 2 + (E ω) ^ 2) := by positivity
  change ‖(G ω) ^ 2‖ ≤ ‖2 * ((R ω) ^ 2 + (E ω) ^ 2)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hLeft, abs_of_nonneg hRight]
  exact hSq
