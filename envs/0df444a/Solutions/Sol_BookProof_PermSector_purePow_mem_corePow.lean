-- Prove2me | solution 1 for BookProof.PermSector.purePow_mem_corePow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:15.321635+00:00
-- url     : https://prove2.me/submissions/5f53b3f4-6337-4919-80bc-66a12f1f2ae8

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.purePow_mem_corePow
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (n : ℕ) (f : Fin n → D₂),
    (∀ i, ((f i : Hs.carrier)) ∈ D) →
      purePow (domSpace Hs D₂) n f ∈ corePow Hs D₂ D n := by

  intro n
  induction n with
  | zero => intro f _; trivial
  | succ n ih =>
      intro f hf
      rw [purePow_succ]
      exact tmul_mem_corePow Hs D₂ D (hf 0) (ih (Fin.tail f) (fun i => hf i.succ))
