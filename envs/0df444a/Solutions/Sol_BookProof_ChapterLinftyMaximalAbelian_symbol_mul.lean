-- Prove2me | solution 1 for BookProof.ChapterLinftyMaximalAbelian.symbol_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:35:03.226113+00:00
-- url     : https://prove2.me/submissions/755f9f71-456b-45d2-9acd-74b22e5d71d4

-- Generated from ChapterLinftyMaximalAbelian.lean — solution of BookProof.ChapterLinftyMaximalAbelian.symbol_mul
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_ae_eq
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian



noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T)
    (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    ((T (multOp φ hφ (oneLp μ))) : α → ℂ) =ᵐ[μ] fun x => φ x * symbol T x := by

  have h := congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => S (oneLp μ)) (hT φ hφ)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at h
  rw [h]
  filter_upwards [multOp_coeFn φ hφ (T (oneLp μ)), symbol_ae_eq T] with x h1 h2
  rw [h1, h2]
