-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_3_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:12:20.279807+00:00
-- url     : https://prove2.me/submissions/ea0cc506-c248-486b-841a-e2e33d10a8b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_13
import Theorems.Thm_BLTCounting_AccuracySpace_claim_3_14

open Matrix BLTCounting.AccuracySpace
open scoped ComplexOrder

namespace AuxLemma316

lemma eig_nonneg_of_posSemidef {K : ℕ} {B : Matrix (Fin K) (Fin K) ℂ}
    (hPSD : B.PosSemidef) (i : Fin K) :
    0 ≤ hPSD.isHermitian.eigenvalues i :=
  hPSD.eigenvalues_nonneg i

lemma eig_le_one_of_one_sub_posSemidef {K : ℕ} {B : Matrix (Fin K) (Fin K) ℂ}
    (hB : B.IsHermitian) (h1B : (1 - B).PosSemidef) (i : Fin K) :
    hB.eigenvalues i ≤ 1 := by
  let v : Fin K → ℂ := (hB.eigenvectorBasis i).ofLp
  have hv_norm : ∑ j : Fin K, ‖v j‖ ^ 2 = 1 := by
    have hnorm : ‖hB.eigenvectorBasis i‖ = 1 := hB.eigenvectorBasis.orthonormal.1 i
    have hsq : ‖hB.eigenvectorBasis i‖ ^ 2 = ∑ j : Fin K, ‖v j‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    rw [hnorm, one_pow] at hsq
    exact hsq.symm
  have h1 : 0 ≤ (star v ⬝ᵥ ((1 - B) *ᵥ v)).re := by
    have hpos := h1B.dotProduct_mulVec_nonneg v
    exact (RCLike.nonneg_iff.mp hpos).1
  have hexp : star v ⬝ᵥ ((1 - B) *ᵥ v) = star v ⬝ᵥ v - star v ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  have hv_dot : (star v ⬝ᵥ v).re = 1 := by
    have hsum : (star v ⬝ᵥ v).re = ∑ j : Fin K, ‖v j‖ ^ 2 := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc : (star (v j) * v j).re = ‖v j‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp [Complex.normSq_apply]
      exact hc
    rw [hsum, hv_norm]
  have heig : hB.eigenvalues i = (star v ⬝ᵥ (B *ᵥ v)).re := hB.eigenvalues_eq i
  rw [hexp, Complex.sub_re, hv_dot, ← heig] at h1
  linarith

lemma trace_B_sub_sq_eq_sum_eig {K : ℕ} {B : Matrix (Fin K) (Fin K) ℂ} (hB : B.IsHermitian) :
    ((B - B * B).trace).re = ∑ i : Fin K, hB.eigenvalues i * (1 - hB.eigenvalues i) := by
  have htrB : B.trace = ∑ i : Fin K, ((hB.eigenvalues i : ℝ) : ℂ) := hB.trace_eq_sum_eigenvalues
  have hB2 : (B * B).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hB.eq]
  have htrB2 : (B * B).trace = ∑ i : Fin K, (((hB.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    have hspec := hB.spectral_theorem
    let U : Matrix (Fin K) (Fin K) ℂ := (hB.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℂ)
    have hU : U * star U = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
    have hU' : star U * U = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
    have hA : B = U * Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) * star U := by
      simpa [U, Unitary.conjStarAlgAut_apply] using hspec
    have hAA : B * B = U * Matrix.diagonal (fun i => ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)) * star U := by
      calc
        B * B = (U * Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) * star U) *
            (U * Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) * star U) := by rw [← hA]
        _ = U * Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) * (star U * U) *
            Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) * star U := by
          simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues) *
            Matrix.diagonal (Complex.ofReal ∘ hB.eigenvalues)) * star U := by
          rw [hU', Matrix.mul_one]
          simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)) * star U := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 2
          ext i
          simp [Function.comp, sq]
    rw [hAA, Matrix.trace_mul_cycle, hU', Matrix.one_mul, Matrix.trace_diagonal]
  rw [Matrix.trace_sub, htrB, htrB2, Complex.sub_re]
  simp only [Complex.re_sum, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

end AuxLemma316

theorem solution :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (K : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi → X₀ ≤ (K : ℝ) * θ →
      ∃ hB : (bandMatrix K θ).IsHermitian,
        (K : ℝ) * θ / Real.pi - C * Real.log ((K : ℝ) * θ) ≤
          (eigCountAtLeast hB (1 / 2) : ℝ) := by
  rcases claim_3_14 with ⟨C₁₄, X₀, hC₁₄, h14⟩
  refine ⟨2 * C₁₄, X₀, by positivity, fun K θ hθ0 hθπ hX₀ => ?_⟩
  have h13 := lemma_3_13 K θ hθ0 hθπ
  have hPSD : (bandMatrix K θ).PosSemidef := h13.1.1
  have h1PSD : (1 - bandMatrix K θ).PosSemidef := h13.1.2
  have hB : (bandMatrix K θ).IsHermitian := hPSD.isHermitian
  refine ⟨hB, ?_⟩
  have htrB : ((bandMatrix K θ).trace).re = (K : ℝ) * θ / Real.pi := by
    rw [h13.2.1.1]
    simp
  have hsum_eig : ∑ i : Fin K, hB.eigenvalues i = (K : ℝ) * θ / Real.pi := by
    have h := hB.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  let S_ge := Finset.univ.filter (fun i : Fin K => (1 / 2 : ℝ) ≤ hB.eigenvalues i)
  let S_lt := Finset.univ.filter (fun i : Fin K => ¬ ((1 / 2 : ℝ) ≤ hB.eigenvalues i))
  have hsplit : ∑ i : Fin K, hB.eigenvalues i =
      (∑ i ∈ S_ge, hB.eigenvalues i) + (∑ i ∈ S_lt, hB.eigenvalues i) := by
    simpa [S_ge, S_lt] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin K => (1 / 2 : ℝ) ≤ hB.eigenvalues i) hB.eigenvalues).symm
  have hge_le : (∑ i ∈ S_ge, hB.eigenvalues i) ≤ (eigCountAtLeast hB (1 / 2) : ℝ) := by
    calc
      (∑ i ∈ S_ge, hB.eigenvalues i) ≤ ∑ _i ∈ S_ge, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => AuxLemma316.eig_le_one_of_one_sub_posSemidef hB h1PSD i
      _ = (S_ge.card : ℝ) := by simp
      _ = (eigCountAtLeast hB (1 / 2) : ℝ) := rfl
  have hlt_le : (∑ i ∈ S_lt, hB.eigenvalues i) ≤
      2 * ∑ i : Fin K, hB.eigenvalues i * (1 - hB.eigenvalues i) := by
    calc
      (∑ i ∈ S_lt, hB.eigenvalues i)
          ≤ ∑ i ∈ S_lt, 2 * (hB.eigenvalues i * (1 - hB.eigenvalues i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hlt : hB.eigenvalues i < 1 / 2 := not_le.mp (Finset.mem_filter.mp hi).2
        have hnn : 0 ≤ hB.eigenvalues i := AuxLemma316.eig_nonneg_of_posSemidef hPSD i
        nlinarith
      _ = 2 * ∑ i ∈ S_lt, hB.eigenvalues i * (1 - hB.eigenvalues i) := by
        rw [← Finset.mul_sum]
      _ ≤ 2 * ∑ i : Fin K, hB.eigenvalues i * (1 - hB.eigenvalues i) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => ?_
        have hnn := AuxLemma316.eig_nonneg_of_posSemidef hPSD i
        have hle1 := AuxLemma316.eig_le_one_of_one_sub_posSemidef hB h1PSD i
        exact mul_nonneg hnn (sub_nonneg.mpr hle1)
  have hdefect_eq := AuxLemma316.trace_B_sub_sq_eq_sum_eig hB
  have hdefect_le : ((bandMatrix K θ - bandMatrix K θ * bandMatrix K θ).trace).re ≤
      C₁₄ * Real.log ((K : ℝ) * θ) :=
    le_trans (Complex.re_le_norm _) (h14 K θ hθ0 hθπ hX₀)
  linarith
