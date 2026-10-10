-- Prove2me | solution 1 for BookProof.KernelBound.kernel_hs_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:19:22.069986+00:00
-- url     : https://prove2.me/submissions/3365941c-2299-4991-acef-b4cf7d8deb38

-- Generated from ChapterKernelBound.lean — solution of BookProof.KernelBound.kernel_hs_sq_bound
import Mathlib
import Definitions.Def_ChapterKernelBound
import Theorems.Thm_BookProof_KernelBound_kernel_row_bound
open BookProof.KernelBound




open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

set_option maxHeartbeats 1000000 in
theorem solution (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) :
    ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2
      ≤ (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2) := by

  exact le_trans ( Finset.sum_le_sum fun y _ => kernel_row_bound Ψ Φ y ) (
      by simp [ Finset.sum_mul _ _ _ ] )
