-- Prove2me | solution 1 for BookProof.PermSector.permOp_mem_sectorDom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:45:59.705982+00:00
-- url     : https://prove2.me/submissions/0029a9a7-e94f-44b7-8764-00139b742f7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.permOp_mem_sectorDom
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_inclPow_permOp
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier}
    (hx : x ∈ sectorDom Hs D₂ n) : permOp Hs n σ x ∈ sectorDom Hs D₂ n := by

  obtain ⟨t, rfl⟩ := hx
  exact ⟨permOp (domSpace Hs D₂) n σ t, inclPow_permOp Hs D₂ n σ t⟩
