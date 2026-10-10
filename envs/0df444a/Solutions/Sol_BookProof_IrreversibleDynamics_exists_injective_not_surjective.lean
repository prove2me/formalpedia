-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.exists_injective_not_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:17:38.865574+00:00
-- url     : https://prove2.me/submissions/1d4a35c3-b4f2-4163-8462-bdd20c99d329

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.exists_injective_not_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [Infinite α] :
    ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f := by

  classical
  obtain e := Infinite.natEmbedding α
  set S : Set α := Set.range e with hS
  refine ⟨fun x => if hx : x ∈ S then e (Classical.choose hx + 1) else x, ?_, ?_⟩
  · intro x y hxy
    simp only at hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · rw [dif_pos hx, dif_pos hy] at hxy
      have cx := Classical.choose_spec hx
      have cy := Classical.choose_spec hy
      have h1 : Classical.choose hx + 1 = Classical.choose hy + 1 := e.injective hxy
      have h2 : Classical.choose hx = Classical.choose hy := by omega
      rw [← cx, ← cy, h2]
    · rw [dif_pos hx, dif_neg hy] at hxy
      exact absurd (hxy ▸ ⟨_, rfl⟩ : y ∈ S) hy
    · rw [dif_neg hx, dif_pos hy] at hxy
      exact absurd (hxy ▸ ⟨_, rfl⟩ : x ∈ S) hx
    · rw [dif_neg hx, dif_neg hy] at hxy; exact hxy
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj (e 0)
    simp only at hx
    by_cases hxs : x ∈ S
    · rw [dif_pos hxs] at hx
      have : Classical.choose hxs + 1 = 0 := e.injective hx
      omega
    · rw [dif_neg hxs] at hx
      exact hxs (hx ▸ ⟨_, rfl⟩)
