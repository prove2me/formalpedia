-- Prove2me | solution 1 for BookProof.ChapterG.dampedFlow_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:19:00.789305+00:00
-- url     : https://prove2.me/submissions/271de4bf-3ba8-4dde-8304-f84ecea8deb9

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.dampedFlow_add
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • M) = NormedSpace.exp (s • M) * NormedSpace.exp (t • M) := by

  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl M).smul_left s |>.smul_right t)
