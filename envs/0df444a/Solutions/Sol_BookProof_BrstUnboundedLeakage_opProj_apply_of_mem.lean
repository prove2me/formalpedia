-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.opProj_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:49:41.92921+00:00
-- url     : https://prove2.me/submissions/0ac16d73-6219-40e2-822f-e0b64d0fb3ad

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.opProj_apply_of_mem
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_eq_self_of_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_opProj_apply
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution {x : H} (hx : x ∈ V) :
    opProj T V hV x = T.op ⟨x, hV hx⟩ := by

  have hsub : (⟨projOp V x, hV (projOp_apply_mem V x)⟩ : T.domain) = ⟨x, hV hx⟩ :=
    Subtype.ext (projOp_eq_self_of_mem V hx)
  rw [opProj_apply, hsub]
