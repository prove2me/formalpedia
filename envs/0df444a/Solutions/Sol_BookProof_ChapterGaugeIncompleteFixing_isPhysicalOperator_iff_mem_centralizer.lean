-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:32:31.825347+00:00
-- url     : https://prove2.me/submissions/f6fd1b4d-11ae-4a44-bcbf-44a5fbdd79ae

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]
variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (U : G → (H →L[ℂ] H))
    (A : H →L[ℂ] H) :
    IsPhysicalOperator U A ↔ A ∈ Subalgebra.centralizer ℂ (Set.range U) := by

  constructor
  · rintro hA _ ⟨g, rfl⟩
    exact (hA g).symm
  · intro hA g
    exact (hA (U g) ⟨g, rfl⟩).symm
