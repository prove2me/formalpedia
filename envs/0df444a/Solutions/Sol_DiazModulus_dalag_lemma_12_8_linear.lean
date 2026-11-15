-- Prove2me | solution 1 for DiazModulus.dalag_lemma_12_8_linear
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:33:38.560296+00:00
-- url     : https://prove2.me/submissions/d83ce268-0d1d-476b-80ed-e395a6a67c22

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_matrix_rank_map_field

open Complex ComplexConjugate

/-! # Lemma 12.8 in the generality of its proof

Let `M = Σⱼ eⱼNⱼ` with `e₁, …, e_m` free over `k` and `Nⱼ` over `k`, and let `φ : K → kⁿ` be `k`-linear and
injective on the span of the `eⱼ`. The images `cⱼ = φ(eⱼ)` are then free, so `v ↦ Σⱼ vⱼcⱼ` is injective and
has a `k`-linear left inverse `G`. The `k`-algebra map `λ₀ : Zⱼ ↦ Σᵢ (cⱼ)ᵢXᵢ` from `k[Z]` to `k[X]` has the left
inverse `Xᵢ ↦ Σ_q G(εᵢ)_q Z_q`, so it is injective and extends to a field homomorphism `Λ : k(Z) → k(X)`.
Since `φ(M_ab) = Σⱼ (Nⱼ)_ab cⱼ`, `Λ` sends `Σⱼ ZⱼNⱼ` to the matrix `φ(M)` with entries `Σᵢ φ(M_ab)ᵢXᵢ`.
A homomorphism of fields does not change the rank of a matrix, which gives the equality. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] {d l m n : ℕ}
    (M : Matrix (Fin d) (Fin l) K) (e : Fin m → K) (he : LinearIndependent k e)
    (N : Fin m → Matrix (Fin d) (Fin l) k) (hMN : M = ∑ j, e j • (N j).map (algebraMap k K))
    (φ : K →ₗ[k] (Fin n → k)) (hφ : Set.InjOn φ (Submodule.span k (Set.range e) : Set K)) :
    (M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (∑ i, MvPolynomial.C (φ x i) * MvPolynomial.X i)).rank =
    (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  classical
  let c : Fin m → (Fin n → k) := fun j => φ (e j)
  -- B3.1: the images are free
  have hc : LinearIndependent k c := by
    have hdisj : Disjoint (Submodule.span k (Set.range e)) (LinearMap.ker φ) := by
      rw [Submodule.disjoint_def]
      intro x hx hker
      exact hφ hx (Submodule.zero_mem _) (by simpa using hker)
    exact he.map hdisj
  -- B1.2: T v = Σ vⱼ cⱼ is injective, with a linear left inverse G
  have hT : LinearMap.ker (Fintype.linearCombination k c) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp hc)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective _ hT
  have hGc : ∀ j, G (c j) = Pi.single j 1 := by
    intro j
    have h1 : Fintype.linearCombination k c (Pi.single j 1) = c j := by
      simp [Fintype.linearCombination_apply, Pi.single_apply]
    rw [← h1, ← LinearMap.comp_apply, hG, LinearMap.id_apply]
  -- B1.3–4: λ₀ (Zⱼ ↦ uⱼ) has the left inverse μ₀ (Xᵢ ↦ Σₗ G(εᵢ)ₗ Zₗ)
  let lam₀ : (MvPolynomial (Fin m) k) →ₐ[k] (MvPolynomial (Fin n) k) := MvPolynomial.aeval fun j => ∑ i, MvPolynomial.C (c j i) * MvPolynomial.X i
  let mu₀ : (MvPolynomial (Fin n) k) →ₐ[k] (MvPolynomial (Fin m) k) :=
    MvPolynomial.aeval fun i => ∑ q, MvPolynomial.C (G (Pi.single i 1) q) * MvPolynomial.X q
  have hcomb : ∀ j q, ∑ i, c j i * G (Pi.single i 1) q = (Pi.single j 1 : Fin m → k) q := by
    intro j q
    have hsum : ∑ i, c j i • (Pi.single i 1 : Fin n → k) = c j := by
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    calc ∑ i, c j i * G (Pi.single i 1) q = G (∑ i, c j i • (Pi.single i 1 : Fin n → k)) q := by
          simp [map_sum, map_smul, Finset.sum_apply]
      _ = G (c j) q := by rw [hsum]
      _ = _ := by rw [hGc j]
  have hml : mu₀.comp lam₀ = AlgHom.id k (MvPolynomial (Fin m) k) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, lam₀, mu₀, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ q, ∑ i, MvPolynomial.C (c j i) * (MvPolynomial.C (G (Pi.single i 1) q) * MvPolynomial.X q) =
        MvPolynomial.C ((Pi.single j 1 : Fin m → k) q) * (MvPolynomial.X q : (MvPolynomial (Fin m) k)) := by
      intro q
      rw [← hcomb j q, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    simp only [this, Pi.single_apply, apply_ite MvPolynomial.C, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hlam₀ : Function.Injective lam₀ := by
    intro a b h
    have h' := congrArg mu₀ h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hml] at h'
  -- B2: the field homomorphism Λ
  let Λ : (FractionRing (MvPolynomial (Fin m) k)) →+* (FractionRing (MvPolynomial (Fin n) k)) := IsLocalization.map (FractionRing (MvPolynomial (Fin n) k)) (lam₀ : (MvPolynomial (Fin m) k) →+* (MvPolynomial (Fin n) k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hlam₀)
  have hΛC : ∀ q : k, Λ (algebraMap k (FractionRing (MvPolynomial (Fin m) k)) q) = algebraMap k (FractionRing (MvPolynomial (Fin n) k)) q := by
    intro q
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)), IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))]
    simp only [Λ, IsLocalization.map_eq, AlgHom.coe_toRingHom, AlgHom.commutes]
  have hΛX : ∀ j, Λ (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) =
      algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)) (∑ i, MvPolynomial.C (c j i) * MvPolynomial.X i) := by
    intro j
    simp only [Λ, IsLocalization.map_eq, AlgHom.coe_toRingHom, lam₀, MvPolynomial.aeval_X]
  -- B3.2: φ(M) = Σ uⱼ Nⱼ
  have hφM : ∀ a b, φ (M a b) = ∑ j, N j a b • c j := by
    intro a b
    rw [hMN]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul]
  -- B3.3: Λ(N(Z)) = φ(M)
  have key : (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).map Λ =
      M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)) (∑ i, MvPolynomial.C (φ x i) * MvPolynomial.X i) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hΛC, hΛX,
      hφM, Finset.sum_apply, Pi.smul_apply]
    simp only [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)), MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum]
    congr 1
    simp only [map_sum, Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- B3.4
  rw [← key, DiazModulus.matrix_rank_map_field Λ]
