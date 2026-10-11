-- Prove2me | solution 1 for BookProof.TwoParticleSector.exists_ne_zero_fermionic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:09.773464+00:00
-- url     : https://prove2.me/submissions/87bfcdae-37d7-4471-a472-05721e136b66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.exists_ne_zero_fermionic
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_mem_fermionic_iff
import Theorems.Thm_BookProof_TensorCore_inner_tmul_pow
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hD : D ≤ D₂) {a b : Hs.carrier} (haD : a ∈ D) (hbD : b ∈ D)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : (inner ℂ a b : ℂ) = 0) :
    ∃ x : redDom (fermionicProj Hs) (sectorCore Hs D₂ D 2), x ≠ 0 := by

  set a' : D₂ := ⟨a, hD haD⟩ with ha'
  set b' : D₂ := ⟨b, hD hbD⟩ with hb'
  set w : (Hs.pow 2).carrier := a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (1 : ℂ)) with hw
  set v : (Hs.pow 2).carrier :=
    a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (1 : ℂ)) - b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] (1 : ℂ)) with hv
  have hcore : v ∈ sectorCore Hs D₂ D 2 := by
    have h1 : (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (1 : ℂ)) : (Hs.pow 2).carrier) ∈ sectorCore Hs D₂ D 2 :=
      ⟨a' ⊗ₜ[ℂ] (b' ⊗ₜ[ℂ] (1 : ℂ)),
        tmul_mem_corePow Hs D₂ D haD (tmul_mem_corePow Hs D₂ D hbD (by trivial)), rfl⟩
    have h2 : (b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] (1 : ℂ)) : (Hs.pow 2).carrier) ∈ sectorCore Hs D₂ D 2 :=
      ⟨b' ⊗ₜ[ℂ] (a' ⊗ₜ[ℂ] (1 : ℂ)),
        tmul_mem_corePow Hs D₂ D hbD (tmul_mem_corePow Hs D₂ D haD (by trivial)), rfl⟩
    exact Submodule.sub_mem _ h1 h2
  have hsec : v ∈ sector (fermionicProj Hs) := by
    refine (mem_fermionic_iff Hs).mpr ?_
    rw [hv, map_sub, swapH_tmul, swapH_tmul]
    abel
  have hba : (inner ℂ b a : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) hab
    rwa [inner_conj_symm, map_zero] at this
  have hone : (inner ℂ ((1 : ℂ) : (Hs.pow 0).carrier) ((1 : ℂ) : (Hs.pow 0).carrier) : ℂ)
      = 1 := by
    show (inner ℂ (1 : ℂ) (1 : ℂ) : ℂ) = 1
    simp
  have hinner : (inner ℂ v w : ℂ) = inner ℂ a a * inner ℂ b b := by
    rw [hv, hw, inner_sub_left, inner_tmul_pow Hs 1, inner_tmul_pow Hs 1,
      inner_tmul_pow Hs 0, inner_tmul_pow Hs 0, hba, hone]
    ring
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hinner
    have ha : (inner ℂ a a : ℂ) ≠ 0 := inner_self_ne_zero.mpr ha0
    have hb : (inner ℂ b b : ℂ) ≠ 0 := inner_self_ne_zero.mpr hb0
    exact (mul_ne_zero ha hb) hinner.symm
  refine ⟨⟨⟨v, hsec⟩, hcore⟩, ?_⟩
  intro h
  exact hv0 (by simpa using congrArg Subtype.val (congrArg Subtype.val h))
