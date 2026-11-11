-- Prove2me | solution 1 for BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T12:44:40.891075+00:00
-- url     : https://prove2.me/submissions/57237df2-0129-4fbf-ab7d-bd0a898b9106

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_cbosonic_inc
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.SecondQuantizationCore
open BookProof.DirectSumEsa

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : hbosonicFockDom Hs D, x ≠ 0 := by

  classical
  obtain ⟨y, hy0⟩ := exists_ne_zero_cbosonic_inc Hs D n haD ha0
  refine ⟨⟨lp.single 2 n ((y : sector (cbosonicProj Hs n))),
    single_mem_dsCore (D := fun n : ℕ => redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))
      n y⟩, ?_⟩
  intro h
  refine hy0 (Subtype.ext ?_)
  have h0 := congrArg (fun z : hbosonicFockDom Hs D =>
    ((z : hbosonicFock Hs) : ∀ n, ↥(sector (cbosonicProj Hs n))) n) h
  simpa using h0
