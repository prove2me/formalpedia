-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:35:55.863201+00:00
-- url     : https://prove2.me/submissions/0a28868c-1815-4a86-9098-a89eb2f6ce92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianAtomicCondensation.lean — solution of BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_commutes_atomProj_iff
open BookProof.ChapterAbelianAtomicCondensation



open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

set_option maxHeartbeats 1000000 in
theorem solution {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp := by

  intro T hT
  obtain ⟨d, hd⟩ := (commutes_atomProj_iff T).1
    (fun i => hA.abelian T hT (atomProj i) (hA.atoms_mem i))
  exact ⟨d, hd.symm⟩
