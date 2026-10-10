-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_mapsTo_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:04:17.445565+00:00
-- url     : https://prove2.me/submissions/4e68d7ce-352f-4848-bb8d-cacbb44f2071

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_mapsTo_unitInterval
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal


@[simp] private theorem dissipative_apply (x : ℝ) : dissipative x = x / 2 := rfl

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.MapsTo dissipative (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by

  intro x hx
  simp only [Set.mem_Icc, dissipative_apply] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]
