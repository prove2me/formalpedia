-- Prove2me | solution 1 for BookProof.PermSector.exists_ne_zero_fermionic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:18.997433+00:00
-- url     : https://prove2.me/submissions/4beaabba-d393-4c57-8687-b807abbb5a58

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.exists_ne_zero_fermionic
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_mem_fermionicSector_iff
import Theorems.Thm_BookProof_PermSector_purePow_mem_sectorCore
import Theorems.Thm_BookProof_TensorPerm_inner_purePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hD : D ≤ D₂) (f : Fin n → Hs.carrier)
    (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0)
    (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : redDom (fermionicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0 := by

  classical
  have hsq : ∀ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
    intro τ
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  have hmul : ∀ σ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign (σ * τ) : ℤ) : ℂ)
      = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) := by
    intro σ τ
    rw [map_mul, Units.val_mul]
    push_cast
    ring
  set v : (Hs.pow n).carrier :=
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • purePow Hs n (f ∘ σ) with hv
  have hcore : v ∈ sectorCore Hs D₂ D n := by
    refine Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ ?_)
    exact purePow_mem_sectorCore Hs D₂ D n _ hD (fun i => hfD (σ i))
  have hsec : v ∈ sector (fermionicProj Hs n) := by
    refine (mem_fermionicSector_iff Hs n).mpr (fun τ => ?_)
    rw [hv, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective (fun σ => σ * τ) (Group.mulRight_bijective τ) _ _ (fun σ => ?_)
    have hcomp : (f ∘ ⇑σ) ∘ ⇑τ = f ∘ ⇑(σ * τ) := by
      funext i
      rfl
    have hlhs : permOp Hs n τ (((Equiv.Perm.sign σ : ℤ) : ℂ) • purePow Hs n (f ∘ ⇑σ))
        = ((Equiv.Perm.sign σ : ℤ) : ℂ) • purePow Hs n (f ∘ ⇑(σ * τ)) := by
      rw [map_smul, permOp_purePow, hcomp]
    have hscal : ((Equiv.Perm.sign τ : ℤ) : ℂ)
        * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ))
        = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
      calc ((Equiv.Perm.sign τ : ℤ) : ℂ)
            * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ))
          = ((Equiv.Perm.sign σ : ℤ) : ℂ)
              * (((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) := by ring
        _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by rw [hsq τ, mul_one]
    rw [hlhs, smul_smul, hmul σ τ, hscal]
  have hinner : (inner ℂ v (purePow Hs n f) : ℂ) = ∏ i, inner ℂ (f i) (f i) := by
    rw [hv, sum_inner]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [inner_smul_left]
      simp only [Units.val_one, Int.cast_one, map_one, one_mul, Equiv.Perm.coe_one,
        Function.comp_id]
      rw [inner_purePow]
    · intro σ _ hσ
      rw [inner_smul_left, inner_purePow]
      have hex : ∃ i, σ i ≠ i := by
        by_contra hcon
        push_neg at hcon
        exact hσ (Equiv.ext (fun i => by simpa using hcon i))
      obtain ⟨i, hi⟩ := hex
      have hzero : (inner ℂ ((f ∘ σ) i) (f i) : ℂ) = 0 := hortho (σ i) i hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hinner
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hinner.symm
    exact (inner_self_ne_zero.mpr (hf0 i)) hi
  refine ⟨⟨⟨v, hsec⟩, hcore⟩, ?_⟩
  intro h
  exact hv0 (by simpa using congrArg Subtype.val (congrArg Subtype.val h))
