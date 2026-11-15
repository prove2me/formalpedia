-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_23
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:08:08.756422+00:00
-- url     : https://prove2.me/submissions/4c8dd2e9-4fd5-4193-ad3b-b1ab2d02e5c5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_cor_12_22
import Theorems.Thm_DiazModulus_baker_rat_add_logAlg_free
import Theorems.Thm_DiazModulus_matrix_rank_map_field

open Complex ComplexConjugate

/-! # DALAG Cor. 12.23: a matrix over `ℚ + ℒ` has rank at least half its structural rank

Let `M = Σ_k e_k N_k` with `e_k ∈ ℚ + ℒ` rationally free and `N_k` rational matrices. By Baker's
theorem in its `ℚ + ℒ` form, the `e_k` are also free over the algebraic numbers `Q̄`. Viewing each
`N_k` over `Q̄` gives a `Q̄`-presentation of `M`, and every entry of `M` lies in `ℒ̃`, since each
`e_k = q_k · 1 + (e_k − q_k)` does. The corollary for matrices over `ℒ̃` then bounds the rank of
`Σ_k X_k N_k` over `Q̄(X₁, …, X_m)` by twice the rank of `M`. The coefficientwise inclusion
`ℚ[X] → Q̄[X]` is injective, so it extends to a homomorphism of fraction fields `ℚ(X) → Q̄(X)`,
which fixes each `X_k` and every rational number; it sends `Σ_k X_k N_k` over `ℚ(X)` to the same
matrix over `Q̄(X)`. A homomorphism of fields does not change the rank of a matrix, so the rank over
`ℚ(X)` is the rank over `Q̄(X)`, at most twice the rank of `M`. -/

namespace RC4_C1223
open DiazModulus

/-- Every element of `ℚ + ℒ` lies in `ℒ̃`. -/
theorem mem_logAlgTilde {z : ℂ} (hz : ∃ q : ℚ, z - q ∈ LogAlg) : z ∈ LogAlgTilde := by
  obtain ⟨q, hq⟩ := hz
  have h1 : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)
  have h2 : z - q ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert_of_mem _ hq)
  have h3 := LogAlgTilde.smul_mem ((q : ℚ) : ↥Qbar) h1
  rw [Subfield.smul_def] at h3
  have hz : z = (((q : ℚ) : ↥Qbar) : ℂ) * 1 + (z - q) := by push_cast; ring
  rw [hz]
  exact LogAlgTilde.add_mem h3 h2

end RC4_C1223

open DiazModulus RC4_C1223 in
theorem solution {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (e : Fin m → ℂ) (he : LinearIndependent ℚ e) (heL : ∀ k, ∃ q : ℚ, e k - q ∈ LogAlg)
    (N : Fin m → Matrix (Fin d) (Fin l) ℚ)
    (hMN : M = ∑ k, e k • (N k).map ((↑) : ℚ → ℂ)) :
    (∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).rank ≤ 2 * M.rank := by
  classical
  -- Baker: `e` is free over `Q̄`
  have he' : LinearIndependent (↥Qbar) e := DiazModulus.baker_rat_add_logAlg_free e he heL
  -- the same presentation, read over `Q̄`
  let N' : Fin m → Matrix (Fin d) (Fin l) ↥Qbar := fun k => (N k).map (algebraMap ℚ ↥Qbar)
  have hMN' : M = ∑ k, e k • (N' k).map ((↑) : ↥Qbar → ℂ) := by
    rw [hMN]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  -- the entries of `M` lie in `ℒ̃`
  have hM : ∀ i j, M i j ∈ LogAlgTilde := by
    intro i j
    rw [hMN]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h := LogAlgTilde.smul_mem ((N k i j : ℚ) : ↥Qbar) (mem_logAlgTilde (heL k))
    rw [Subfield.smul_def] at h
    convert h using 1
    push_cast
    ring
  have hB3 := DiazModulus.dalag_cor_12_22 M hM e he' N' hMN'
  -- the coefficientwise inclusion `ℚ(X) → Q̄(X)`
  let ι : MvPolynomial (Fin m) ℚ →+* MvPolynomial (Fin m) ↥Qbar :=
    MvPolynomial.map (algebraMap ℚ ↥Qbar)
  have hι : Function.Injective ι := MvPolynomial.map_injective _ (algebraMap ℚ ↥Qbar).injective
  let Φ : FractionRing (MvPolynomial (Fin m) ℚ) →+* FractionRing (MvPolynomial (Fin m) ↥Qbar) :=
    IsLocalization.map _ ι (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ι hι)
  have hΦX : ∀ k, Φ (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) =
      algebraMap (MvPolynomial (Fin m) ↥Qbar) (FractionRing (MvPolynomial (Fin m) ↥Qbar))
        (MvPolynomial.X k) := by
    intro k
    simp only [Φ, IsLocalization.map_eq, ι, MvPolynomial.map_X]
  have hΦq : ∀ r : ℚ, Φ (algebraMap ℚ _ r) =
      algebraMap ↥Qbar (FractionRing (MvPolynomial (Fin m) ↥Qbar)) (algebraMap ℚ ↥Qbar r) := by
    intro r
    simp only [eq_ratCast, map_ratCast]
  have hmap : (∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).map Φ =
      ∑ k, (algebraMap (MvPolynomial (Fin m) ↥Qbar) (FractionRing (MvPolynomial (Fin m) ↥Qbar))
        (MvPolynomial.X k)) •
      (N' k).map (algebraMap ↥Qbar (FractionRing (MvPolynomial (Fin m) ↥Qbar))) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, hΦX, hΦq, N']
  rw [← DiazModulus.matrix_rank_map_field Φ, hmap]
  exact hB3
