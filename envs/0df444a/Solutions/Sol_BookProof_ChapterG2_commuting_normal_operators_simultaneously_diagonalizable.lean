-- Prove2me | solution 1 for BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:22:09.1334+00:00
-- url     : https://prove2.me/submissions/003eaa39-f757-4c29-ae7f-7fe2f89784cc

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ι : Type*} [Finite ι]
    (T : ι → H →ₗ[ℂ] H) (h_symm : ∀ i, (T i).IsSymmetric)
    (h_comm : ∀ i j, i ≠ j → Commute (T i) (T j)) :
    ⨆ (χ : ι → ℂ), ⨅ i, Module.End.eigenspace (T i) (χ i) = ⊤ :=
  LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute h_symm
      (fun i j hij => h_comm i j hij)
