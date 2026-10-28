-- Prove2me | solution 1 for BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T02:19:25.565997+00:00
-- url     : https://prove2.me/submissions/c6e4a016-3218-469e-a13f-684f59f477e5

-- Generated from ChapterScalarDGammaEsa.lean — solution of BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ScalarDGamma




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

variable (Hs : IPSpace) (c : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : fockSectorDom Hs ⊤ n) :
    ‖fockSectorOp Hs ⊤ (scalarOp Hs c) n x‖ ≤ ((n : ℝ) * |c|) * ‖(x : fockSector Hs n)‖ := by

  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : fockSector Hs n) = sectorEmb Hs n ((⟨x₀, hx₀⟩ : sectorDom Hs ⊤ n) :
      (Hs.pow n).carrier) := hxe.symm
  have hop : fockSectorOp Hs ⊤ (scalarOp Hs c) n x
      = sectorEmb Hs n (sectorOp Hs ⊤ (scalarOp Hs c) n ⟨x₀, hx₀⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs ⊤ (scalarOp Hs c) n) x ⟨x₀, hx₀⟩ hx'
  rw [hop, (sectorEmb Hs n).norm_map, hx', (sectorEmb Hs n).norm_map,
    sectorOp_scalar Hs c n ⟨x₀, hx₀⟩, norm_smul]
  have hc : ‖((n : ℂ) * c)‖ = (n : ℝ) * |c| := by
    rw [norm_mul]
    simp
  rw [hc]
