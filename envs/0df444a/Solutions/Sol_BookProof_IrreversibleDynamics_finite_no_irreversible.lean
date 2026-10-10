-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.finite_no_irreversible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:17:27.419977+00:00
-- url     : https://prove2.me/submissions/5e4eb520-ef9a-43a7-989c-5d4321f24aff

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.finite_no_irreversible
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
import Theorems.Thm_BookProof_IrreversibleDynamics_finite_injective_imp_surjective
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [Finite α] :
    ¬ ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f := by

  rintro ⟨f, hinj, hnsurj⟩
  exact hnsurj (finite_injective_imp_surjective hinj)
