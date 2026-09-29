-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.tendsto_resDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:18:55.184018+00:00
-- url     : https://prove2.me/submissions/6bdde877-bc89-41f1-a377-dd4e51a0a9e2

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.tendsto_resDiff
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (hres : StrongResolventConvergence T S) (y : H) :
    Tendsto (fun n => resDiff T S n y) atTop (𝓝 0) := by

  have h := (hres y).const_sub (T.resCLM 1 y)
  simpa [resDiff] using h
