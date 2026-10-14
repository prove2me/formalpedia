-- Prove2me | solution 1 for BookProof.PermSector.inclPow_permOp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:07.171751+00:00
-- url     : https://prove2.me/submissions/671a8c67-c00e-41e3-bcd6-48dd683ea276
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.inclPow_permOp
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_good_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterFriedrichsExtension
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
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (t : ((domSpace Hs D₂).pow n).carrier) :
    inclPow Hs D₂ n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (inclPow Hs D₂ n t) := (good_permOp Hs D₂ 0 ⊤ n σ).incl t
