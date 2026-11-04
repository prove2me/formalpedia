-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T14:49:22.314071+00:00
-- url     : https://prove2.me/submissions/1aba1852-db17-44c2-92ea-db2bdc4ca3b7

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_kernelOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_summable_tail
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_bound
import Theorems.Thm_BookProof_CarlemanUnboundedHop_not_summable_inv_one_add_nat
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_hasSum_tail
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_isL2Kernel
open BookProof.CarlemanUnboundedHop




open Finset
open BookProof.KernelBound
open BookProof.FarisLavine
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in

theorem solution (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp (geoHop_isL2Kernel b hrho hrho1)) :=
  kernelOp_essentiallySelfAdjoint (A := fun n => 1 + (n : ℝ)) (θ := fun r => rho ^ r)
    (Θ := fun j => rho ^ (j + 1) * (1 - rho)⁻¹) _
    (fun r => by positivity) (geo_hasSum_tail hrho hrho1) (geo_summable_tail hrho hrho1)
    (fun n => by positivity) (fun m n hmn => by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith)
    (fun n k hnk => geoHop_bound hrho n k hnk) not_summable_inv_one_add_nat
