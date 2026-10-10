-- Prove2me | solution 1 for BookProof.ChapterG.exists_complete_gaugeFixing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:22:13.90498+00:00
-- url     : https://prove2.me/submissions/0600350f-d887-4c57-9080-e33815c7ba6c

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.exists_complete_gaugeFixing
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} {π : X → Y}
    (hπ : Function.Surjective π) :
    ∃ S : Set X, IsCompleteGaugeFixing π S ∧ π '' S = Set.univ := by

  refine ⟨Set.range (Function.surjInv hπ), ?_, ?_⟩
  · rintro x x' ⟨y, rfl⟩ ⟨y', rfl⟩ he
    rw [Function.surjInv_eq hπ, Function.surjInv_eq hπ] at he
    rw [he]
  · rw [Set.eq_univ_iff_forall]
    intro y
    exact ⟨Function.surjInv hπ (π (Function.surjInv hπ y)), ⟨_, rfl⟩, by
      rw [Function.surjInv_eq hπ, Function.surjInv_eq hπ]⟩
