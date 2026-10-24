-- Prove2me | solution 1 for FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:03:12.976545+00:00
-- url     : https://prove2.me/submissions/92635971-c89a-4c74-8b1a-38b0fe921c34

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorems.Thm_FunctionalInequalities_Analysis_scalar_log_gap_408915f

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LogDetConcavity
private lemma FunctionalInequalities.Analysis.bounded_spectral_decomposition {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      A = U * diagonal a * Uᵀ ∧
      (∀ i, 0 < a i) ∧ (∀ i, a i ≤ K) ∧
      Real.log A.det = ∑ i, Real.log (a i) := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  let a : Fin n → ℝ := hA.isHermitian.eigenvalues
  have hu : Uᵀ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hu' : U * Uᵀ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have he : A = U * diagonal a * Uᵀ := by
    simpa [U, a, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hA.isHermitian.spectral_theorem
  have ha : ∀ i, 0 < a i := hA.eigenvalues_pos
  have hc : Uᵀ * A * U = diagonal a := by
    calc
      Uᵀ * A * U = (Uᵀ * U) * diagonal a * (Uᵀ * U) := by
        rw [he]
        simp only [Matrix.mul_assoc]
      _ = diagonal a := by rw [hu, one_mul, mul_one]
  have hk : ∀ i, a i ≤ K := by
    intro i
    have hh := hAK.conjTranspose_mul_mul_same U
    have hh' :
        Uᴴ * (K • 1 - A) * U = K • 1 - diagonal a := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        mul_one, hu, hc]
    rw [hh'] at hh
    have hv := hh.diag_nonneg (i := i)
    apply sub_nonneg.mp
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Matrix.diagonal_apply_eq] using hv
  refine ⟨U, a, hu, hu', he, ha, hk, ?_⟩
  have hdet : A.det = ∏ i, a i := by
    simpa [a] using hA.isHermitian.det_eq_prod_eigenvalues
  rw [hdet, Real.log_prod (fun i _ => (ha i).ne')]
private lemma FunctionalInequalities.Analysis.trace_spectral_pair {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    ((U * diagonal a * Uᵀ) * (V * diagonal b * Vᵀ)).trace =
      ∑ i, ∑ j, a i * b j * (Uᵀ * V) i j ^ 2 := by
  calc
    ((U * diagonal a * Uᵀ) * (V * diagonal b * Vᵀ)).trace =
        (U * (diagonal a * Uᵀ * V * diagonal b * Vᵀ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((diagonal a * Uᵀ * V * diagonal b * Vᵀ) * U).trace :=
      Matrix.trace_mul_comm _ _
    _ = (diagonal a * (Uᵀ * V) * diagonal b * (Uᵀ * V)ᵀ).trace := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    _ = ∑ i, ∑ j, a i * b j * (Uᵀ * V) i j ^ 2 := by
      unfold Matrix.trace Matrix.diag
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
      ring
private lemma FunctionalInequalities.Analysis.trace_spectral_square {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hu : Uᵀ * U = 1) :
    ((U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ)).trace =
      ∑ i, a i ^ 2 := by
  have hm :
      (U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ) =
        U * diagonal (fun i => a i ^ 2) * Uᵀ := by
    calc
      (U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ) =
          U * (diagonal a * (Uᵀ * U) * diagonal a) * Uᵀ := by
        simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => a i ^ 2) * Uᵀ := by
        simp only [hu, mul_one, Matrix.diagonal_mul_diagonal, pow_two]
  rw [hm, Matrix.trace_mul_cycle, hu, one_mul, Matrix.trace_diagonal]
private lemma FunctionalInequalities.Analysis.inv_spectral {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hu : Uᵀ * U = 1) (hu' : U * Uᵀ = 1) (ha : ∀ i, 0 < a i) :
    (U * diagonal a * Uᵀ)⁻¹ =
      U * diagonal (fun i => (a i)⁻¹) * Uᵀ := by
  apply Matrix.inv_eq_left_inv
  have hd :
      diagonal (fun i => (a i)⁻¹ * a i) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hv : (fun i => (a i)⁻¹ * a i) = fun _ => (1 : ℝ) :=
      funext fun i => inv_mul_cancel₀ (ha i).ne'
    rw [hv, Matrix.diagonal_one]
  calc
    (U * diagonal (fun i => (a i)⁻¹) * Uᵀ) * (U * diagonal a * Uᵀ) =
        U * (diagonal (fun i => (a i)⁻¹) * (Uᵀ * U) * diagonal a) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hu, mul_one, Matrix.diagonal_mul_diagonal, hd, mul_one, hu']
private lemma FunctionalInequalities.Analysis.orthogonal_row_sq {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * Qᵀ = 1) (i : Fin n) :
    ∑ j, Q i j ^ 2 = 1 := by
  have hh := congrFun (congrFun hQ i) i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← sq,
    Matrix.one_apply_eq] using hh
private lemma FunctionalInequalities.Analysis.frobenius_sub_trace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (∑ i, ∑ j, (B - A) i j ^ 2) =
      (B * B).trace + (A * A).trace - 2 * (A * B).trace := by
  have hd : (B - A)ᵀ = B - A := by
    rw [Matrix.transpose_sub, hB, hA]
  have ht :
      ((B - A) * (B - A)).trace = ∑ i, ∑ j, (B - A) i j ^ 2 := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hij := congrFun (congrFun hd i) j
    change (B - A) j i = (B - A) i j at hij
    rw [hij]
    ring
  rw [← ht]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm B A]
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 800000 in
/-- **Quantitative concavity of `log det`**: for positive definite `A, B ≤ K·Id`,
`log det B + ‖B − A‖²_F / (2K²) ≤ log det A + tr(A⁻¹ (B − A))`. -/
theorem solution {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
    Real.log B.det + (∑ i, ∑ j, (B - A) i j ^ 2) / (2 * K ^ 2) ≤
      Real.log A.det + (A⁻¹ * (B - A)).trace := by
  obtain ⟨U, a, hu, hu', hAd, ha, haK, hAlog⟩ :=
    bounded_spectral_decomposition hA hAK
  obtain ⟨V, b, hv, hv', hBd, hb, hbK, hBlog⟩ :=
    bounded_spectral_decomposition hB hBK
  let Q : Matrix (Fin n) (Fin n) ℝ := Uᵀ * V
  have hQr : Q * Qᵀ = 1 := by
    dsimp [Q]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Uᵀ * V * (Vᵀ * U) = Uᵀ * (V * Vᵀ) * U := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv', mul_one, hu]
  have hQc : Qᵀ * Q = 1 := by
    dsimp [Q]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Vᵀ * U * (Uᵀ * V) = Vᵀ * (U * Uᵀ) * V := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu', mul_one, hv]
  have hr : ∀ i, ∑ j, Q i j ^ 2 = 1 :=
    orthogonal_row_sq Q hQr
  have hc : ∀ j, ∑ i, Q i j ^ 2 = 1 := by
    intro j
    have hh : Qᵀ * (Qᵀ)ᵀ = 1 := by
      rw [Matrix.transpose_transpose]
      exact hQc
    simpa only [Matrix.transpose_apply] using orthogonal_row_sq Qᵀ hh j
  have row_weight (f : Fin n → ℝ) :
      (∑ i, ∑ j, f i * Q i j ^ 2) = ∑ i, f i := by
    simp only [← Finset.mul_sum, hr, mul_one]
  have col_weight (f : Fin n → ℝ) :
      (∑ i, ∑ j, f j * Q i j ^ 2) = ∑ j, f j := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hc, mul_one]
  have hAA : (A * A).trace = ∑ i, a i ^ 2 := by
    rw [hAd]
    exact trace_spectral_square U a hu
  have hBB : (B * B).trace = ∑ j, b j ^ 2 := by
    rw [hBd]
    exact trace_spectral_square V b hv
  have hAB :
      (A * B).trace = ∑ i, ∑ j, a i * b j * Q i j ^ 2 := by
    rw [hAd, hBd]
    exact trace_spectral_pair U V a b
  have hAs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hBs : Bᵀ = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  have hgap :
      (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) =
        ∑ i, ∑ j, (B - A) i j ^ 2 := by
    calc
      (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) =
          ∑ i, ∑ j,
            (b j ^ 2 * Q i j ^ 2 + a i ^ 2 * Q i j ^ 2 -
              2 * (a i * b j * Q i j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i, ∑ j, b j ^ 2 * Q i j ^ 2) +
          (∑ i, ∑ j, a i ^ 2 * Q i j ^ 2) -
          (∑ i, ∑ j, 2 * (a i * b j * Q i j ^ 2)) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ j, b j ^ 2) + (∑ i, a i ^ 2) -
          2 * (∑ i, ∑ j, a i * b j * Q i j ^ 2) := by
        rw [col_weight (fun j => b j ^ 2), row_weight (fun i => a i ^ 2)]
        simp only [← Finset.mul_sum]
      _ = (B * B).trace + (A * A).trace - 2 * (A * B).trace := by
        rw [hAA, hBB, hAB]
      _ = ∑ i, ∑ j, (B - A) i j ^ 2 :=
        (frobenius_sub_trace A B hAs hBs).symm
  have hAi :
      A⁻¹ = U * diagonal (fun i => (a i)⁻¹) * Uᵀ := by
    rw [hAd]
    exact inv_spectral U a hu hu' ha
  have hAiB :
      (A⁻¹ * B).trace = ∑ i, ∑ j, (a i)⁻¹ * b j * Q i j ^ 2 := by
    rw [hAi, hBd]
    exact trace_spectral_pair U V (fun i => (a i)⁻¹) b
  have hAiA : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hone :
      (∑ i, ∑ j, (1 : ℝ) * Q i j ^ 2) =
        (1 : Matrix (Fin n) (Fin n) ℝ).trace := by
    rw [row_weight (fun _ => (1 : ℝ))]
    simp
  have htangent :
      (∑ i, ∑ j, ((b j - a i) / a i) * Q i j ^ 2) =
        (A⁻¹ * (B - A)).trace := by
    calc
      (∑ i, ∑ j, ((b j - a i) / a i) * Q i j ^ 2) =
          ∑ i, ∑ j,
            ((a i)⁻¹ * b j * Q i j ^ 2 - 1 * Q i j ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        field_simp [(ha i).ne']
      _ = (∑ i, ∑ j, (a i)⁻¹ * b j * Q i j ^ 2) -
          (∑ i, ∑ j, (1 : ℝ) * Q i j ^ 2) := by
        simp only [Finset.sum_sub_distrib]
      _ = (A⁻¹ * B).trace - (1 : Matrix (Fin n) (Fin n) ℝ).trace := by
        rw [hAiB, hone]
      _ = (A⁻¹ * (B - A)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub, hAiA]
  have hdiv :
      (∑ i, ∑ j, ((b j - a i) ^ 2 / (2 * K ^ 2)) * Q i j ^ 2) =
        (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) / (2 * K ^ 2) := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs :
      (∑ i, ∑ j,
        (Real.log (b j) + (b j - a i) ^ 2 / (2 * K ^ 2)) * Q i j ^ 2) ≤
      ∑ i, ∑ j,
        (Real.log (a i) + (b j - a i) / a i) * Q i j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (FunctionalInequalities.Analysis.scalar_log_gap_408915f (ha i) (hb j) (haK i) (hbK j))
      (sq_nonneg (Q i j))
  simp only [add_mul, Finset.sum_add_distrib] at hs
  rw [col_weight (fun j => Real.log (b j)),
    row_weight (fun i => Real.log (a i)),
    hdiv, hgap, htangent, ← hBlog, ← hAlog] at hs
  exact hs
