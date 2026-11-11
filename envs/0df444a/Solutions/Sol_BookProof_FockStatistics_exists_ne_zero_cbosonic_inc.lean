-- Prove2me | solution 1 for BookProof.FockStatistics.exists_ne_zero_cbosonic_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T10:27:18.849639+00:00
-- url     : https://prove2.me/submissions/494497c5-3550-4159-9042-6669e7df313d

-- Generated from ChapterFockStatisticsCompletion.lean — solution of BookProof.FockStatistics.exists_ne_zero_cbosonic_inc
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Theorems.Thm_BookProof_FockStatistics_sectorEmb_mem_cbosonicSector_inc
import Theorems.Thm_BookProof_PermSector_exists_ne_zero_bosonic
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.GroupAverage.UnitaryRep
open BookProof.FockStatistics




open BookProof.GroupAverage BookProof.ReducedEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.FarisLavine
open BookProof.PermSector
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n), x ≠ 0 := by

  obtain ⟨y, hy0⟩ := exists_ne_zero_bosonic Hs D D n le_rfl haD ha0
  set v : (Hs.pow n).carrier := ((y : sector (bosonicProj Hs n)) : (Hs.pow n).carrier) with hv
  have hvsec : v ∈ sector (bosonicProj Hs n) := (y : sector (bosonicProj Hs n)).2
  have hvdom : v ∈ sectorDom Hs D n := sectorCore_le_sectorDom Hs D D n y.2
  have hv0 : v ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext (Subtype.ext h))
  refine ⟨⟨⟨sectorEmb Hs n v, sectorEmb_mem_cbosonicSector Hs n hvsec⟩,
    ⟨v, hvdom, rfl⟩⟩, ?_⟩
  intro h
  refine hv0 ((sectorEmb Hs n).injective ?_)
  have := congrArg Subtype.val (congrArg Subtype.val h)
  simpa using this
