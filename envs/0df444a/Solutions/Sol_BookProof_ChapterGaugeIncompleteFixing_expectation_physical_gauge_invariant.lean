-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:32:44.585295+00:00
-- url     : https://prove2.me/submissions/19aa2347-0fb3-4411-833f-7dde71a96fa0

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
import Theorems.Thm_BookProof_ChapterG_expectation_gauge_invariant
import Theorems.Thm_BookProof_ChapterG_expectation_gauge_invariant
open BookProof
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]
variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {U : G → (H →L[ℂ] H)}
    (hU : IsGaugeUnitaryFamily U) {A : H →L[ℂ] H} (hA : IsPhysicalOperator U A)
    (g : G) (Ψ : H) :
    ⟪U g Ψ, A (U g Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ := ChapterG.expectation_gauge_invariant (U g) (hU g) A (hA g) Ψ
