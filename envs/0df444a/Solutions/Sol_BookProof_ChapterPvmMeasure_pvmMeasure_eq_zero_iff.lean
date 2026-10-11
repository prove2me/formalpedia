-- Prove2me | solution 1 for BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:38.230532+00:00
-- url     : https://prove2.me/submissions/92b951f6-768f-4d34-9d0d-686890d174f0

-- Generated from ChapterPvmMeasure.lean — solution of BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterPvmMeasure
open BookProof.ChapterPvmMeasure



open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (P : Pvm X H)
variable (P : Pvm X H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution {E : Set X} (hE : MeasurableSet E) :
    pvmMeasure P ψ E = 0 ↔ P.p E ψ = 0 := by

  rw [pvmMeasure_apply P ψ hE, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have : ‖P.p E ψ‖ ^ 2 = 0 := le_antisymm h (by positivity)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    simp [h]
