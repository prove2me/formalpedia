-- Prove2me | solution 1 for BookProof.KernelBound.kernel_contraction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:19:46.113825+00:00
-- url     : https://prove2.me/submissions/c92d4eb3-c01c-4017-91ca-9e7021f16b0c

-- Generated from ChapterKernelBound.lean — solution of BookProof.KernelBound.kernel_contraction
import Mathlib
import Definitions.Def_ChapterKernelBound
import Theorems.Thm_BookProof_KernelBound_kernel_hs_sq_bound
open BookProof.KernelBound




open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

set_option maxHeartbeats 1000000 in
theorem solution (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜)
    (hΨ : ∑ y, ∑ x, ‖Ψ y x‖ ^ 2 = 1) :
    ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ ∑ x, ‖Φ x‖ ^ 2 := by

  simpa [ hΨ ] using kernel_hs_sq_bound Ψ Φ
