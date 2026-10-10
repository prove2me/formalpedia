-- Prove2me | solution 1 for BookProof.KernelBound.kernel_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:19:34.36936+00:00
-- url     : https://prove2.me/submissions/e6e225ae-6eee-4746-a699-8fd3502cd5a8

-- Generated from ChapterKernelBound.lean — solution of BookProof.KernelBound.kernel_l2_bound
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
theorem solution (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) :
    Real.sqrt (∑ y, ‖kernelOp Ψ Φ y‖ ^ 2)
      ≤ Real.sqrt (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * Real.sqrt (∑ x, ‖Φ x‖ ^ 2) := by

  rw [ ← Real.sqrt_mul <| Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ;
      exact Real.sqrt_le_sqrt <| by simpa only [kernelOp] using kernel_hs_sq_bound _ _;
