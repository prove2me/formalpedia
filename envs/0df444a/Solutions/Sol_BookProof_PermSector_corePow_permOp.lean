-- Prove2me | solution 1 for BookProof.PermSector.corePow_permOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:09.884833+00:00
-- url     : https://prove2.me/submissions/35c7860c-2aec-4bcb-8f40-79f856a3686e

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.corePow_permOp
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_good_permOp
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
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    {t : ((domSpace Hs D₂).pow n).carrier} (ht : t ∈ corePow Hs D₂ D n) :
    permOp (domSpace Hs D₂) n σ t ∈ corePow Hs D₂ D n := (good_permOp Hs D₂ 0 D n σ).core t ht
