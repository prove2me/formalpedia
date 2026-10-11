-- Prove2me | solution 1 for BookProof.TensorCore.inner_tmul_pow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:06.71369+00:00
-- url     : https://prove2.me/submissions/31c68afd-304f-492a-91c7-0a42ae6a392a

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.inner_tmul_pow
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x x' : Hs.carrier) (y y' : (Hs.pow n).carrier) :
    (inner ℂ (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) (x' ⊗ₜ[ℂ] y') : ℂ)
      = inner ℂ x x' * inner ℂ y y' := TensorProduct.inner_tmul ℂ x x' y y'
