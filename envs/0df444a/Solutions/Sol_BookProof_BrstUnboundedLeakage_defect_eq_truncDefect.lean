-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.defect_eq_truncDefect
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:50:47.262622+00:00
-- url     : https://prove2.me/submissions/d37c3bda-0ca5-4e66-97f5-4f3591396aa7

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.defect_eq_truncDefect
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_opProj_apply_of_mem
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution {y : H} (hy : y ∈ V) :
    T.op ⟨y, hV hy⟩ - BookProof.BrstUnboundedLeakage.truncGen T V hV y = truncDefect T V hV y := by

  have h1 : opProj T V hV y = T.op ⟨y, hV hy⟩ := opProj_apply_of_mem T V hV hy
  simp [truncDefect, BookProof.BrstUnboundedLeakage.truncGen, ContinuousLinearMap.sub_apply, h1]
