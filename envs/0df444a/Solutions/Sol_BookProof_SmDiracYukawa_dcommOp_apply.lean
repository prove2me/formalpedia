-- Prove2me | solution 1 for BookProof.SmDiracYukawa.dcommOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:08:28.841706+00:00
-- url     : https://prove2.me/submissions/5c06918f-3c95-44e0-bcfd-08b4975e6098

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.dcommOp_apply
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (H N : FermiFock n →ₗ[ℂ] FermiFock n) (ψ : FermiFock n) :
    dcommOp H N ψ = N (N (H ψ)) - N (H (N ψ)) - (N (H (N ψ)) - H (N (N ψ))) := by

  simp [dcommOp, Ring.lie_def]
