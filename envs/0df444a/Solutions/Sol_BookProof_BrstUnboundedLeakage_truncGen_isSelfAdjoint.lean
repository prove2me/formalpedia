-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:09:03.321033+00:00
-- url     : https://prove2.me/submissions/dee4fcf6-5869-4136-ae1c-033a5ebed6cc

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_inner
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent
open BookProof.BrstLeakage
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution : IsSelfAdjoint (truncGen T V hV) := by

  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hx : (projOp V x) ∈ V := projOp_apply_mem V x
  have hy : (projOp V y) ∈ V := projOp_apply_mem V y
  have hstep :
      ⟪T.op ⟨projOp V x, hV hx⟩, (projOp V y : H)⟫_ℂ
        = ⟪(projOp V x : H), T.op ⟨projOp V y, hV hy⟩⟫_ℂ :=
    T.symmetric ⟨projOp V x, hV hx⟩ ⟨projOp V y, hV hy⟩
  have hl : ⟪truncGen T V hV x, y⟫_ℂ = ⟪T.op ⟨projOp V x, hV hx⟩, (projOp V y : H)⟫_ℂ := by
    have : truncGen T V hV x = projOp V (T.op ⟨projOp V x, hV hx⟩) := rfl
    rw [this, projOp_inner]
  have hr : ⟪x, truncGen T V hV y⟫_ℂ = ⟪(projOp V x : H), T.op ⟨projOp V y, hV hy⟩⟫_ℂ := by
    have : truncGen T V hV y = projOp V (T.op ⟨projOp V y, hV hy⟩) := rfl
    rw [this, ← projOp_inner]
  have hgoal : ⟪truncGen T V hV x, y⟫_ℂ = ⟪x, truncGen T V hV y⟫_ℂ := by
    rw [hl, hr, hstep]
  exact hgoal
