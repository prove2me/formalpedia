-- Prove2me | solution 1 for BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T12:35:53.103108+00:00
-- url     : https://prove2.me/submissions/060157c7-7146-44e0-a4c0-fb3f5756227c

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_cfermionic_inc
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
theorem solution (n : ℕ) (f : Fin n → Hs.carrier)
    (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0)
    (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : hfermionicFockDom Hs D, x ≠ 0 := by

  classical
  obtain ⟨y, hy0⟩ := exists_ne_zero_cfermionic_inc Hs D n f hfD hf0 hortho
  refine ⟨⟨lp.single 2 n ((y : sector (cfermionicProj Hs n))),
    single_mem_dsCore (D := fun n : ℕ => redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))
      n y⟩, ?_⟩
  intro h
  refine hy0 (Subtype.ext ?_)
  have h0 := congrArg (fun z : hfermionicFockDom Hs D =>
    ((z : hfermionicFock Hs) : ∀ n, ↥(sector (cfermionicProj Hs n))) n) h
  simpa using h0
