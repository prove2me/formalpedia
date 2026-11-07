-- Prove2me | solution 1 for BookProof.ChapterStoneTheorem.stone_bijection
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T11:40:54.465558+00:00
-- url     : https://prove2.me/submissions/babdd447-2497-4310-a419-cd757aa74f17

-- Generated from ChapterStoneTheorem.lean — solution of BookProof.ChapterStoneTheorem.stone_bijection
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_ext_prime
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_ext_prime
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_gen_stoneGroup_eq
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_eq
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneTheorem
open BookProof.ChapterStoneResolvent



open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Bijective (fun T : UnboundedSelfAdjoint H => T.stoneGroup) := by

  constructor
  · intro T S h
    have h' : T.stoneGroup = S.stoneGroup := h
    rw [← T.gen_stoneGroup_eq, ← S.gen_stoneGroup_eq, h']
  · exact fun G => ⟨G.gen, WeakMeasurableUnitaryGroup.ext_prime (fun t => G.gen_stoneU_eq t)⟩
