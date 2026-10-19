-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.norm_restartIter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:28:34.829454+00:00
-- url     : https://prove2.me/submissions/f112c85a-b419-48ab-bbec-70cbd01f0b9d

import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_BrstUnboundedLeakage_restartGen_isSelfAdjoint
import Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.norm_restartIter
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)
variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)


theorem solution (τ : ℝ) (x : H) (n : ℕ) :
    ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ‖BookProof.BrstLeakage.flow (restartGen T Vs hVs k) τ
      (leakageIter (restartGen T Vs hVs) τ x k)‖ = ‖x‖
    rw [BookProof.BrstLeakage.norm_flow_apply
      (BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint T Vs hVs k), ih]

