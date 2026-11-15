-- Prove2me | solution 1 for DiazModulus.dalag_lemma_12_9_dehomog
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:33:41.469213+00:00
-- url     : https://prove2.me/submissions/bdc0a03d-3d40-4325-b45e-c7d895efb446

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_matrix_rank_map_field

open Complex ComplexConjugate

/-! # Dehomogenisation does not change the structural rank

Let `A = N₀ + Σᵢ XᵢNᵢ` over `k(X₁, …, X_m)` and `B = Y₀N₀ + Σᵢ YᵢNᵢ` over `k(Y₀, …, Y_m)`. The `k`-algebra
map `θ₀ : Y₀ ↦ Y₀, Yᵢ ↦ Y₀Yᵢ (i ≥ 1)` of `k[Y]` has the left inverse `Y₀ ↦ Y₀, Yᵢ ↦ Yᵢ/Y₀` into `k(Y)`, so it
is injective and extends to a field homomorphism `θ` of `k(Y)`. The renaming `Xᵢ ↦ Yᵢ` is injective and
extends to a field homomorphism `ι : k(X) → k(Y)`. Entrywise, `θ(B) = Y₀ · ι(A)`. A homomorphism of fields
does not change the rank of a matrix, nor does multiplication by the non-zero scalar `Y₀`, so
`rank B = rank θ(B) = rank ι(A) = rank A`. -/

open DiazModulus in
theorem solution {k : Type*} [Field k] {d l m : ℕ} (N₀ : Matrix (Fin d) (Fin l) k)
    (N : Fin m → Matrix (Fin d) (Fin l) k) :
    (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin m) k))) +
      ∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank =
    (∑ j : Fin (m + 1),
      (algebraMap (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k))
        (MvPolynomial.X j)) •
      ((Fin.cons N₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) k) j).map
        (algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)))).rank := by
  classical
  let y : Fin (m + 1) → (FractionRing (MvPolynomial (Fin (m + 1)) k)) := fun i => algebraMap (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k)) (MvPolynomial.X i)
  have hY0 : y 0 ≠ 0 := by
    intro h
    exact MvPolynomial.X_ne_zero (R := k) (0 : Fin (m + 1))
      ((IsFractionRing.injective (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k))) (h.trans (map_zero _).symm))
  -- θ₀ : Y₀ ↦ Y₀, Yᵢ₊₁ ↦ Y₀ Yᵢ₊₁ ; ρ₀ : Y₀ ↦ Y₀, Yᵢ₊₁ ↦ Yᵢ₊₁ / Y₀
  let θ₀ : (MvPolynomial (Fin (m + 1)) k) →ₐ[k] (MvPolynomial (Fin (m + 1)) k) := MvPolynomial.aeval
    (Fin.cons (MvPolynomial.X 0) fun i => MvPolynomial.X 0 * MvPolynomial.X i.succ)
  let ρ₀ : (MvPolynomial (Fin (m + 1)) k) →ₐ[k] (FractionRing (MvPolynomial (Fin (m + 1)) k)) := MvPolynomial.aeval (Fin.cons (y 0) fun i => y i.succ / y 0)
  have hρθ : ρ₀.comp θ₀ = IsScalarTower.toAlgHom k (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [θ₀, ρ₀, y]
    · simp only [AlgHom.comp_apply, θ₀, ρ₀, MvPolynomial.aeval_X, Fin.cons_succ, map_mul, Fin.cons_zero,
        IsScalarTower.coe_toAlgHom']
      exact mul_div_cancel₀ _ hY0
  have hθ₀ : Function.Injective θ₀ := by
    intro a b h
    have h' : (ρ₀.comp θ₀) a = (ρ₀.comp θ₀) b := by simp only [AlgHom.comp_apply, h]
    rw [hρθ] at h'
    exact IsFractionRing.injective (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k)) h'
  let θ : (FractionRing (MvPolynomial (Fin (m + 1)) k)) →+* (FractionRing (MvPolynomial (Fin (m + 1)) k)) := IsLocalization.map (FractionRing (MvPolynomial (Fin (m + 1)) k)) (θ₀ : (MvPolynomial (Fin (m + 1)) k) →+* (MvPolynomial (Fin (m + 1)) k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hθ₀)
  let ι₀ : (MvPolynomial (Fin m) k) →ₐ[k] (MvPolynomial (Fin (m + 1)) k) := MvPolynomial.rename Fin.succ
  have hι₀ : Function.Injective ι₀ := MvPolynomial.rename_injective _ (Fin.succ_injective _)
  let ι : (FractionRing (MvPolynomial (Fin m) k)) →+* (FractionRing (MvPolynomial (Fin (m + 1)) k)) := IsLocalization.map (FractionRing (MvPolynomial (Fin (m + 1)) k)) (ι₀ : (MvPolynomial (Fin m) k) →+* (MvPolynomial (Fin (m + 1)) k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hι₀)
  have hθC : ∀ c : k, θ (algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)) c) = algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k))]
    simp only [θ, IsLocalization.map_eq, AlgHom.coe_toRingHom, AlgHom.commutes]
  have hθ0 : θ (y 0) = y 0 := by
    simp only [θ, y, IsLocalization.map_eq, AlgHom.coe_toRingHom, θ₀, MvPolynomial.aeval_X, Fin.cons_zero]
  have hθs : ∀ i : Fin m, θ (y i.succ) = y 0 * y i.succ := by
    intro i
    simp only [θ, y, IsLocalization.map_eq, AlgHom.coe_toRingHom, θ₀, MvPolynomial.aeval_X, Fin.cons_succ,
      map_mul]
  have hιC : ∀ c : k, ι (algebraMap k (FractionRing (MvPolynomial (Fin m) k)) c) = algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)), IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k))]
    simp only [ι, IsLocalization.map_eq, AlgHom.coe_toRingHom, AlgHom.commutes]
  have hιX : ∀ i, ι (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X i)) = y i.succ := by
    intro i
    simp only [ι, y, IsLocalization.map_eq, AlgHom.coe_toRingHom, ι₀, MvPolynomial.rename_X]
  have key : (∑ j : Fin (m + 1), y j •
      ((Fin.cons N₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) k) j).map (algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)))).map θ =
      y 0 • (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin m) k))) +
        ∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).map ι := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_sum,
      map_mul, map_add, hθC, hθ0, hθs, hιC, hιX, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hrank : (∑ j : Fin (m + 1), y j •
      ((Fin.cons N₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) k) j).map (algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)))).rank =
      (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin m) k))) +
        ∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
    rw [← DiazModulus.matrix_rank_map_field θ, key,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hY0),
      DiazModulus.matrix_rank_map_field ι]
  exact hrank.symm
