-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:22.570882+00:00
-- url     : https://prove2.me/submissions/97c99809-7b01-4ab6-95ec-f0e0e9fc82f3

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma_irreducible
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_scalar
import Theorems.Thm_BookProof_ChapterA3_toEuclideanLin_mul4
import Theorems.Thm_BookProof_ChapterA3_mgammaLin_orthogonal_invariant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (W : Submodule ℂ MajoranaSpace)
    (hW : ∀ μ, ∀ x ∈ W, mgammaLin μ x ∈ W) : W = ⊥ ∨ W = ⊤ := by

  set p : MajoranaSpace →ₗ[ℂ] MajoranaSpace :=
    (W.starProjection : MajoranaSpace →L[ℂ] MajoranaSpace).toLinearMap with hp
  have hpself : ∀ x ∈ W, p x = x := fun x hx => Submodule.starProjection_eq_self_iff.mpr hx
  have hpzero : ∀ x ∈ Wᗮ, p x = 0 := by
    intro x hx
    simp [hp, Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hx]
  have hpmem : ∀ x, p x ∈ W := fun x => (W.orthogonalProjection x).2
  have hcomm : ∀ μ, p ∘ₗ mgammaLin μ = mgammaLin μ ∘ₗ p := by
    intro μ
    refine LinearMap.ext fun x => ?_
    have ha : p x ∈ W := hpmem x
    have hb : x - p x ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hsplit : mgammaLin μ x = mgammaLin μ (p x) + mgammaLin μ (x - p x) := by
      rw [← map_add]; congr 1; abel
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hsplit, map_add,
      hpself _ (hW μ _ ha), hpzero _ (mgammaLin_orthogonal_invariant hW μ hb), add_zero]
  set M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.toEuclideanLin.symm p with hMdef
  have hMp : Matrix.toEuclideanLin M = p := Matrix.toEuclideanLin.apply_symm_apply p
  have hMcomm : ∀ μ, M * mgamma μ = mgamma μ * M := by
    intro μ
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul4, toEuclideanLin_mul4, hMp]
    exact hcomm μ
  have hM := mgamma_commutant_scalar M hMcomm
  have hpx : ∀ x, p x = (M 0 0) • x := by
    intro x
    rw [← hMp, hM]
    simp
  obtain ⟨v, hv⟩ := exists_ne (0 : MajoranaSpace)
  have hidem : (M 0 0) * (M 0 0) = M 0 0 := by
    have h1 : p (p v) = p v := hpself _ (hpmem v)
    rw [hpx, hpx, smul_smul] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← sub_smul] at h2
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h
    · exact absurd h hv
  have hcase : (M 0 0) = 0 ∨ (M 0 0) = 1 := by
    rcases mul_eq_zero.mp (show (M 0 0) * ((M 0 0) - 1) = 0 by linear_combination hidem) with
      h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hcase with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' := hpself x hx
    rw [hpx, h, zero_smul] at hx'
    exact hx'.symm
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hx' := hpmem x
    rwa [hpx, h, one_smul] at hx'
