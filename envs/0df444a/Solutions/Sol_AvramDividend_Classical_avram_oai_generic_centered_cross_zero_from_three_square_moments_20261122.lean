-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_generic_centered_cross_zero_from_three_square_moments_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:30:36.537797+00:00
-- url     : https://prove2.me/submissions/fbba944e-dbcc-4393-9411-4e8b90ebc727

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y Z : Ω → ℝ) (a b : ℝ)
    (hY : Integrable (fun ω => (Y ω) ^ 2) P)
    (hZ : Integrable (fun ω => (Z ω) ^ 2) P)
    (hSum : Integrable (fun ω => (Y ω + Z ω) ^ 2) P)
    (hEY : (∫ ω, (Y ω) ^ 2 ∂P) = a)
    (hEZ : (∫ ω, (Z ω) ^ 2 ∂P) = b)
    (hESum : (∫ ω, (Y ω + Z ω) ^ 2 ∂P) = a + b) :
    Integrable (fun ω => Y ω * Z ω) P ∧
    (∫ ω, Y ω * Z ω ∂P) = 0  := by
  let W : Ω → ℝ := fun ω => ((Y ω + Z ω) ^ 2 - Y ω ^ 2 - Z ω ^ 2) / 2
  have hW : Integrable W P :=
    ((hSum.sub hY).sub hZ).div_const 2
  have hEq : (fun ω => Y ω * Z ω) = W := by
    funext ω
    dsimp [W]
    ring
  have hYZ : Integrable (fun ω => Y ω * Z ω) P := by
    rw [hEq]
    exact hW
  refine ⟨hYZ, ?_⟩
  have hWInt : (∫ ω, W ω ∂P) =
      (((∫ ω, (Y ω + Z ω) ^ 2 ∂P) -
          (∫ ω, (Y ω) ^ 2 ∂P) -
          (∫ ω, (Z ω) ^ 2 ∂P)) / 2) := by
    have hScale : W = (fun ω =>
        (1 / 2 : ℝ) * ((Y ω + Z ω) ^ 2 - Y ω ^ 2 - Z ω ^ 2)) := by
      funext ω
      dsimp [W]
      ring
    rw [hScale, integral_const_mul]
    have hA := integral_sub (hSum.sub hY) hZ
    have hB := integral_sub hSum hY
    simp only [Pi.sub_apply] at hA hB
    rw [hB] at hA
    rw [hA]
    ring
  rw [hEq, hWInt, hESum, hEY, hEZ]
  ring
