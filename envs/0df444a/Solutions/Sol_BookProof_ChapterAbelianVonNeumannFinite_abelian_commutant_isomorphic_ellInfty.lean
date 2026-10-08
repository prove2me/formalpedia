-- Prove2me | solution 1 for BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:38.942276+00:00
-- url     : https://prove2.me/submissions/a2842116-39ed-48c9-9755-77bc73d22fa7

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

namespace BookProof.ChapterAbelianVonNeumannFinite
theorem commutes_diagonal_iff (e : n → ℂ) (he : Function.Injective e) (M : Matrix n n ℂ) :
    M * diagonal e = diagonal e * M ↔ ∃ d : n → ℂ, M = diagonal d := by
  constructor
  · intro h
    refine ⟨fun i => M i i, ?_⟩
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · have hthis := congrFun (congrFun h i) j
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, mul_ite, ite_mul, zero_mul, mul_zero,
        Finset.sum_ite_eq] at hthis
      have hne : e j - e i ≠ 0 := sub_ne_zero.mpr (fun hc => hij (he hc).symm)
      have hzero : M i j * (e j - e i) = 0 := by ring_nf; linear_combination hthis
      have hMij : M i j = 0 := (mul_eq_zero.mp hzero).resolve_right hne
      simp [Matrix.diagonal_apply_ne _ hij, hMij]
  · rintro ⟨d, rfl⟩
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp [mul_comm]

@[simp] theorem diagonalStarAlgHom_apply (d : n → ℂ) :
    (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) d = diagonal d := rfl

theorem diagonalStarAlgHom_injective :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by
  intro d d' h
  funext i
  have := congrFun (congrFun h i) i
  simpa using this

@[simp] theorem conjDiagonal_apply (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
    conjDiagonal U d = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) (diagonal d) := rfl

theorem conjDiagonal_injective (U : Matrix.unitaryGroup n ℂ) :
    Function.Injective (conjDiagonal U) := by
  intro d d' h
  refine diagonalStarAlgHom_injective ?_
  simpa [conjDiagonal_apply] using
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U).injective h

theorem commutant_eq_range_conjDiagonal {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdist : Function.Injective hA.eigenvalues) :
    {M : Matrix n n ℂ | M * A = A * M} = Set.range (conjDiagonal hA.eigenvectorUnitary) := by
  classical
  set c := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary with hc
  set e : n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with he
  have hAeq : A = c (diagonal e) := hA.spectral_theorem
  have heinj : Function.Injective e := by
    intro i j hij
    exact hdist (by simpa [he, Complex.ofReal_inj] using hij)
  ext M
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    have h' : c.symm M * diagonal e = diagonal e * c.symm M := by
      have h1 : c.symm (M * A) = c.symm M * c.symm A := map_mul _ _ _
      have h2 : c.symm (A * M) = c.symm A * c.symm M := map_mul _ _ _
      have hcA : c.symm A = diagonal e := by rw [hAeq]; exact c.symm_apply_apply _
      rw [hcA] at h1 h2
      rw [← h1, ← h2, h]
    obtain ⟨d, hd⟩ := (commutes_diagonal_iff e heinj (c.symm M)).1 h'
    refine ⟨d, ?_⟩
    rw [conjDiagonal_apply, ← hc, ← hd, c.apply_symm_apply]
  · rintro ⟨d, rfl⟩
    have hcomm : diagonal d * diagonal e = diagonal e * diagonal d := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      simp [mul_comm]
    have hc2 := congrArg c hcomm
    rw [map_mul, map_mul] at hc2
    rw [conjDiagonal_apply, ← hc, hAeq]
    exact hc2
end BookProof.ChapterAbelianVonNeumannFinite

theorem solution {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdist : Function.Injective hA.eigenvalues) :
    ∃ f : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ,
      Function.Injective f ∧ Set.range f = {M : Matrix n n ℂ | M * A = A * M} :=
  ⟨conjDiagonal hA.eigenvectorUnitary, conjDiagonal_injective _,
    (commutant_eq_range_conjDiagonal hA hdist).symm⟩

#print axioms solution

