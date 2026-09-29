-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:17:21.513507+00:00
-- url     : https://prove2.me/submissions/9450626c-ebce-4da1-aa69-b915f3102536

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T S : UnboundedSelfAdjoint H) (y : T.domain) :
    S.op ⟨S.resCLM 1 (y : H), S.resCLM_mem 1 (y : H)⟩ - S.resCLM 1 (T.op y)
      = T.resCLM 1 (T.shift 1 y) - S.resCLM 1 (T.shift 1 y) := by

  have h1 : S.op ⟨S.resCLM 1 (y : H), S.resCLM_mem 1 (y : H)⟩
      = (y : H) + ((1 : ℂ) * Complex.I) • (S.resCLM 1 (y : H)) := by
    have := S.op_res (l := 1) one_ne_zero (y : H)
    simpa using this
  have h2 : T.op y = T.shift 1 y + ((1 : ℂ) * Complex.I) • (y : H) := by
    rw [T.shift_apply]
    push_cast
    abel
  have h3 : T.resCLM 1 (T.shift 1 y) = (y : H) := by
    have := T.res_shift (l := 1) one_ne_zero y
    simpa using congrArg (fun (x : T.domain) => (x : H)) this
  rw [h1, h2, h3, map_add, ContinuousLinearMap.map_smul]
  abel
