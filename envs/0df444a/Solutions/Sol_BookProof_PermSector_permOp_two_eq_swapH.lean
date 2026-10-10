-- Prove2me | solution 1 for BookProof.PermSector.permOp_two_eq_swapH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:59:46.854403+00:00
-- url     : https://prove2.me/submissions/2681f5c0-3968-46eb-ab62-7bb35fc04430

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.permOp_two_eq_swapH
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (x : (Hs.pow 2).carrier) :
    permOp Hs 2 (Equiv.swap 0 1) x = BookProof.TwoParticleSector.swapH Hs x := by

  have h : ((permOp Hs 2 (Equiv.swap 0 1)).toLinearEquiv.toLinearMap :
      (Hs.pow 2).carrier →ₗ[ℂ] (Hs.pow 2).carrier) = BookProof.TwoParticleSector.swapH Hs := by
    refine linearMap_ext_purePow Hs (fun f => ?_)
    change permOp Hs 2 (Equiv.swap 0 1) (purePow Hs 2 f)
      = BookProof.TwoParticleSector.swapH Hs (purePow Hs 2 f)
    have hsw : BookProof.TwoParticleSector.swapH Hs (purePow Hs 2 f)
        = swapFirst Hs 0 (purePow Hs 2 f) := rfl
    rw [permOp_purePow, hsw, swapFirst_purePow]
  exact LinearMap.congr_fun h x
