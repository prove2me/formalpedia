-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_real_square_difference_energy_identity_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:02:39.581544+00:00
-- url     : https://prove2.me/submissions/4b555567-17c0-4610-8cd3-e1fc1161aab0

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- The exact original measure second moment of a real variable difference. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : Ω → ℝ)
    (hU : Integrable (fun ω => (U ω)^2) P)
    (hV : Integrable (fun ω => (V ω)^2) P)
    (hUV : Integrable (fun ω => U ω * V ω) P) :
    Integrable (fun ω => (U ω - V ω)^2) P ∧
      (∫ ω, (U ω - V ω)^2 ∂P) =
      (∫ ω, (U ω)^2 ∂P) + (∫ ω, (V ω)^2 ∂P) -
        2 * (∫ ω, U ω * V ω ∂P) := by
  have hCross : Integrable (fun ω => (2 : ℝ) * (U ω * V ω)) P :=
    hUV.const_mul 2
  have hPoly : (fun ω => (U ω - V ω)^2) =
      (fun ω => (U ω)^2 + (V ω)^2 - 2 * (U ω * V ω)) := by
    funext ω
    ring
  rw [hPoly]
  constructor
  · exact (hU.add hV).sub hCross
  · calc
      (∫ ω, ((U ω)^2 + (V ω)^2 - 2 * (U ω * V ω)) ∂P) =
          (∫ ω, ((U ω)^2 + (V ω)^2) ∂P) -
            (∫ ω, 2 * (U ω * V ω) ∂P) := by
              exact integral_sub (hU.add hV) hCross
      _ = (∫ ω, (U ω)^2 ∂P) + (∫ ω, (V ω)^2 ∂P) -
            2 * (∫ ω, U ω * V ω ∂P) := by
        rw [integral_add hU hV, integral_const_mul]
