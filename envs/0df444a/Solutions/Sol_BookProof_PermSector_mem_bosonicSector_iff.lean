-- Prove2me | solution 1 for BookProof.PermSector.mem_bosonicSector_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:59:44.527891+00:00
-- url     : https://prove2.me/submissions/34166f47-d8ba-41ef-b05a-b9b9dafaa995

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.mem_bosonicSector_iff
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_mem_range_avgProj_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) {x : (Hs.pow n).carrier} :
    x ∈ sector (bosonicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), permOp Hs n σ x = x := by

  rw [sector, bosonicProj, (permRep Hs n).mem_range_avgProj_iff]
  constructor
  · intro h σ
    simpa using h σ⁻¹
  · intro h σ
    simpa using h σ⁻¹
