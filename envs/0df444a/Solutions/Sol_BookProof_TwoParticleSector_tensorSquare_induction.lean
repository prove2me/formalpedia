-- Prove2me | solution 1 for BookProof.TwoParticleSector.tensorSquare_induction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:57.651304+00:00
-- url     : https://prove2.me/submissions/8d1e5fd1-2cd8-4601-8ce9-601ac8a7ecf0

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.tensorSquare_induction
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    {P : Y ⊗[ℂ] (Y ⊗[ℂ] ℂ) → Prop} (hzero : P 0)
    (htmul : ∀ (x y : Y) (c : ℂ), P (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] c)))
    (hadd : ∀ u v, P u → P v → P (u + v)) (t : Y ⊗[ℂ] (Y ⊗[ℂ] ℂ)) : P t := by

  induction t using TensorProduct.induction_on with
  | zero => exact hzero
  | tmul x b =>
      induction b using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul y c => exact htmul x y c
      | add u v hu hv => rw [TensorProduct.tmul_add]; exact hadd _ _ hu hv
  | add u v hu hv => exact hadd _ _ hu hv
