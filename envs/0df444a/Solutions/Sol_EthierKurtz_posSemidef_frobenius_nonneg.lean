-- Prove2me | solution 1 for EthierKurtz.posSemidef_frobenius_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T22:19:41.005683+00:00
-- url     : https://prove2.me/submissions/6bca5ca6-3640-4208-88a9-66ce0af384be

import Mathlib

open scoped Topology

theorem solution {d : ℕ}
    (A H : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * H i j := by
  have hA' : A.IsHermitian := hA.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ :=
    (hA'.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hUdef
  set lam : Fin d → ℝ := hA'.eigenvalues with hlamdef
  have hspec2 : A = U * (Matrix.diagonal (RCLike.ofReal ∘ lam) :
      Matrix (Fin d) (Fin d) ℝ) * star U := by
    rw [hA'.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hentry : ∀ i j : Fin d, A i j
      = ∑ k : Fin d, U i k * lam k * U j k := by
    intro i j
    have h1 : A i j = ((U * (Matrix.diagonal (RCLike.ofReal ∘ lam) :
        Matrix (Fin d) (Fin d) ℝ) * star U) i j) := by
      rw [hspec2]
    rw [h1]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.star_apply, star_trivial, RCLike.ofReal_real_eq_id,
      Function.comp_apply, id_eq]
  have hgoal : (∑ i, ∑ j, A i j * H i j)
      = ∑ k : Fin d, lam k * (∑ i, ∑ j, U i k * U j k * H i j) := by
    have e : ∀ i j : Fin d, A i j * H i j
        = ∑ k : Fin d, lam k * (U i k * U j k * H i j) := by
      intro i j
      rw [hentry i j, Finset.sum_mul]
      congr 1
      ext k
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => e i j))]
    have eswap : ∀ F : Fin d → Fin d → Fin d → ℝ,
        (∑ i, ∑ j, ∑ k, F i j k) = ∑ k, ∑ i, ∑ j, F i j k := by
      intro F
      have hinner : (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, F i j k)
          = ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d, F i j k := by
        congr 1
        ext i
        exact Finset.sum_comm
      rw [hinner, Finset.sum_comm]
    rw [eswap]
    congr 1
    ext k
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [Finset.mul_sum]
  rw [hgoal]
  refine Finset.sum_nonneg fun k _ => mul_nonneg
    (Matrix.PosSemidef.eigenvalues_nonneg hA k) ?_
  have hQ := hH.dotProduct_mulVec_nonneg (fun i => U i k)
  simp only [star_trivial] at hQ
  have hmatch : (∑ i, ∑ j, U i k * U j k * H i j)
      = dotProduct (fun i => U i k)
        (Matrix.mulVec H (fun i => U i k)) := by
    simp only [dotProduct, Matrix.mulVec]
    congr 1
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext x
    ring
  rw [hmatch]
  exact hQ
