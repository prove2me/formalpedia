-- Prove2me | solution 1 for DiazModulus.dalag_lemma_12_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:31:29.171769+00:00
-- url     : https://prove2.me/submissions/8c4eb7ae-42f1-41e4-9bad-33bbfc749e70

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_lemma_12_9_dehomog
import Theorems.Thm_DiazModulus_dalag_lemma_12_8_linear

open Complex ComplexConjugate

/-! # DALAG Lemma 12.9

Let `φ : K → k^{n+1}` be `k`-linear and injective on the span of the `eⱼ`, read as a map into the affine forms
`k + kX₁ + ⋯ + kXₙ`. Put `N′ᵢ = (φ(M_ab)ᵢ)_{a,b}` for `i = 0, …, n`. Entrywise, the matrix `φ(M)` with affine
entries is `N′₀ + Σᵢ XᵢN′ᵢ₊₁`, and its homogenisation `Σ_{i=0}^{n} YᵢN′ᵢ` is the matrix with entries
`Σᵢ φ(M_ab)ᵢYᵢ`, the linear-form image of `M` under the same `φ` in `n + 1` variables. Dehomogenisation keeps the
rank, so `rank φ(M) = rank Σ YᵢN′ᵢ`, and the linear form of the lemma gives `rank Σ YᵢN′ᵢ = rank Σⱼ ZⱼNⱼ`. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] {d l m n : ℕ}
    (M : Matrix (Fin d) (Fin l) K) (e : Fin m → K) (he : LinearIndependent k e)
    (N : Fin m → Matrix (Fin d) (Fin l) k) (hMN : M = ∑ j, e j • (N j).map (algebraMap k K))
    (φ : K →ₗ[k] (Fin (n + 1) → k)) (hφ : Set.InjOn φ (Submodule.span k (Set.range e) : Set K)) :
    (M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (MvPolynomial.C (φ x 0) + ∑ i : Fin n, MvPolynomial.C (φ x i.succ) * MvPolynomial.X i)).rank =
    (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  classical
  let N' : Fin (n + 1) → Matrix (Fin d) (Fin l) k := fun i => Matrix.of fun a b => φ (M a b) i
  have h1 := DiazModulus.dalag_lemma_12_9_dehomog (N' 0) (fun i => N' i.succ)
  have h2 := DiazModulus.dalag_lemma_12_8_linear (n := n + 1) M e he N hMN φ hφ
  have hcons : (Fin.cons (N' 0) (fun i => N' i.succ) : Fin (n + 1) → Matrix (Fin d) (Fin l) k) = N' :=
    Fin.cons_self_tail N'
  rw [hcons] at h1
  have hL : (M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (MvPolynomial.C (φ x 0) + ∑ i : Fin n, MvPolynomial.C (φ x i.succ) * MvPolynomial.X i)) =
      (N' 0).map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) +
      ∑ j, (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (MvPolynomial.X j)) • (N' j.succ).map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) := by
    ext a b
    simp only [N', Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
      map_add, map_sum, map_mul, smul_eq_mul, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k),
      MvPolynomial.algebraMap_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hR : (∑ j : Fin (n + 1),
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (FractionRing (MvPolynomial (Fin (n + 1)) k))
        (MvPolynomial.X j)) •
      (N' j).map (algebraMap k (FractionRing (MvPolynomial (Fin (n + 1)) k)))) =
      (M.map fun x => algebraMap (MvPolynomial (Fin (n + 1)) k) (FractionRing (MvPolynomial (Fin (n + 1)) k))
        (∑ i, MvPolynomial.C (φ x i) * MvPolynomial.X i)) := by
    ext a b
    simp only [N', Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
      map_sum, map_mul, smul_eq_mul, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (n + 1)) k),
      MvPolynomial.algebraMap_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hL, h1, hR, h2]
