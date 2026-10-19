-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.wigner_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:00.795818+00:00
-- url     : https://prove2.me/submissions/514b2616-1642-44df-aec1-89cb63d1165d

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.wigner_symmetry
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_wigner_coord
import Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_basis_sum
import Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_sum_smul
import Theorems.Thm_BookProof_ChapterWignerSymmetry_wignerCoord_coordMap
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (b : OrthonormalBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : E → E, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by

  classical
  set G := imgBasis b T o hT with hG
  have hcoord : ∀ (x : E) (k : ι),
      coordMap b T G (fun j => b.repr x j) k = ⟪G k, T x⟫_ℂ := by
    intro x k
    rw [coordMap]
    congr 1
    exact congrArg T (b.sum_repr x)
  have hexp : ∀ x : E, T x = ∑ k, ⟪G k, T x⟫_ℂ • G k := by
    intro x
    conv_lhs => rw [← G.sum_repr (T x)]
    exact Finset.sum_congr rfl fun k _ => by rw [G.repr_apply_apply]
  rcases wigner_coord (wignerCoord_coordMap (b := b) (o := o) hT) with h | h
  · left
    refine ⟨b.repr.trans G.repr.symm, fun x => ?_⟩
    obtain ⟨lam, hlam, hk⟩ := h (fun j => b.repr x j)
    refine ⟨lam, hlam, ?_⟩
    have hU : (b.repr.trans G.repr.symm) x = ∑ k, (b.repr x k) • G k := by
      simpa using (G.sum_repr_symm (b.repr x)).symm
    rw [hU, Finset.smul_sum, hexp x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord x k, hk k, smul_smul]
  · right
    refine ⟨fun x => ∑ k, conj (b.repr x k) • G k, ⟨?_, ?_, ?_, ?_⟩, fun x => ?_⟩
    · intro x y
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [map_add, ← add_smul]; simp
    · intro a x
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_smul]; simp
    · intro x y
      rw [inner_sum_smul G]
      have hxy : ⟪x, y⟫_ℂ = ∑ k, conj (b.repr x k) * (b.repr y k) := by
        conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
        rw [inner_sum_smul b]
      rw [hxy, map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Complex.conj_conj, map_mul, Complex.conj_conj, mul_comm]
    · intro y
      refine ⟨∑ j, conj (G.repr y j) • b j, ?_⟩
      have hrep : ∀ k, b.repr (∑ j, conj (G.repr y j) • b j) k = conj (G.repr y k) := by
        intro k
        rw [b.repr_apply_apply, inner_basis_sum]
      have : ∑ k, conj (b.repr (∑ j, conj (G.repr y j) • b j) k) • G k
          = ∑ k, (G.repr y k) • G k := by
        exact Finset.sum_congr rfl fun k _ => by rw [hrep k, Complex.conj_conj]
      exact this.trans (by simpa using G.sum_repr y)
    · obtain ⟨lam, hlam, hk⟩ := h (fun j => b.repr x j)
      refine ⟨lam, hlam, ?_⟩
      rw [Finset.smul_sum, hexp x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcoord x k, hk k, smul_smul]
