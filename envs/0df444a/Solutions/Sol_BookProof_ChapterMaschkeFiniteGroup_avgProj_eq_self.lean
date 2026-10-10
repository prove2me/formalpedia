-- Prove2me | solution 1 for BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:49:45.97258+00:00
-- url     : https://prove2.me/submissions/c3747185-70cb-4d92-856d-3239f222b192

-- Generated from ChapterMaschkeFiniteGroup.lean — solution of BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_rho_rho
import Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_apply
open BookProof.ChapterMaschkeFiniteGroup




variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x ∈ W, pi x = x) {x : V} (hx : x ∈ W) :
    avgProj ρ pi x = x := by

  have hterm : ∀ g : G, ρ g (pi (ρ g⁻¹ x)) = x := by
    intro g
    have hmem : ρ g⁻¹ x ∈ W := hW g⁻¹ x hx
    rw [hpi _ hmem, rho_rho]
    simp
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [avgProj_apply]
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
