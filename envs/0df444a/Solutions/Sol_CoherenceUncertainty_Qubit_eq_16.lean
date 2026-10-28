-- Prove2me | solution 1 for CoherenceUncertainty.Qubit.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:33:29.183074+00:00
-- url     : https://prove2.me/submissions/e91396d8-8e17-4029-86ad-060d715c91c6

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace Aux_CU_16

open CoherenceUncertainty.Qubit Matrix

lemma entropy_conj (W : MBasis) (q : Fin 2 → ℝ) :
    ShadowTomography.QuantumLB.vnEntropy
      ((W : Mat2) * Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) * star (W : Mat2)) =
      -∑ i, q i * Real.logb 2 (q i) := by
  set D : Mat2 := Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) with hD
  have hDh : D.IsHermitian := by
    rw [hD, Matrix.isHermitian_diagonal_iff]
    intro i; simp [IsSelfAdjoint]
  have hA : ((W : Mat2) * D * star (W : Mat2)).IsHermitian := by
    rw [star_eq_conjTranspose]; exact isHermitian_mul_mul_conjTranspose _ hDh
  have hU1 : star (W : Mat2) * (W : Mat2) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
  have hU2 : (W : Mat2) * star (W : Mat2) = 1 := Matrix.mem_unitaryGroup_iff.mp W.2
  have htr : ((W : Mat2) * D * star (W : Mat2)).trace = ((q 0 + q 1 : ℝ) : ℂ) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, hD, Matrix.trace_diagonal,
      Fin.sum_univ_two]
    push_cast; ring
  have hdet : ((W : Mat2) * D * star (W : Mat2)).det = ((q 0 * q 1 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_mul, hD, Matrix.det_diagonal, Fin.prod_univ_two]
    have : (W : Mat2).det * (star (W : Mat2)).det = 1 := by
      rw [← Matrix.det_mul, hU2, Matrix.det_one]
    push_cast
    linear_combination (↑(q 0) * ↑(q 1) : ℂ) * this
  have hsum := hA.trace_eq_sum_eigenvalues
  have hprod := hA.det_eq_prod_eigenvalues
  rw [htr, Fin.sum_univ_two] at hsum
  rw [hdet, Fin.prod_univ_two] at hprod
  set l0 := hA.eigenvalues 0
  set l1 := hA.eigenvalues 1
  have hs : l0 + l1 = q 0 + q 1 := by
    have : ((q 0 + q 1 : ℝ) : ℂ) = ((l0 + l1 : ℝ) : ℂ) := by rw [hsum]; push_cast; rfl
    exact_mod_cast this.symm
  have hpr : l0 * l1 = q 0 * q 1 := by
    have : ((q 0 * q 1 : ℝ) : ℂ) = ((l0 * l1 : ℝ) : ℂ) := by rw [hprod]; push_cast; rfl
    exact_mod_cast this.symm
  have hq : (l0 - q 0) * (l0 - q 1) = 0 := by
    have : l1 = q 0 + q 1 - l0 := by linarith
    rw [this] at hpr
    linear_combination -hpr
  unfold ShadowTomography.QuantumLB.vnEntropy
  rw [dif_pos hA, Fin.sum_univ_two, Fin.sum_univ_two]
  rcases mul_eq_zero.mp hq with h | h
  · have h0 : l0 = q 0 := by linarith
    have h1 : l1 = q 1 := by linarith
    rw [show hA.eigenvalues 0 = q 0 from h0, show hA.eigenvalues 1 = q 1 from h1]
  · have h0 : l0 = q 1 := by linarith
    have h1 : l1 = q 0 := by linarith
    rw [show hA.eigenvalues 0 = q 1 from h0, show hA.eigenvalues 1 = q 0 from h1]
    ring

lemma conj_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl

end Aux_CU_16

open CoherenceUncertainty.Qubit Matrix Aux_CU_16 in
theorem solution (ρ : Mat2) (hρ : IsDensity ρ) :
    (∃ (p : ℝ) (W : MBasis), 0 ≤ p ∧ p ≤ 1 ∧
      ρ = (W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2)) ∧
    ∀ (p : ℝ) (W : MBasis), 0 ≤ p → p ≤ 1 →
      ρ = (W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2) →
      (∀ (U : MBasis) (i : Fin 2),
          shannon (prob U ρ) = fp p (‖(star (W : Mat2) * (U : Mat2)) 0 i‖ ^ 2)) ∧
        purity ρ = 2 * p ^ 2 - 2 * p + 1 ∧
        ShadowTomography.QuantumLB.vnEntropy ρ = WildeQIT.binaryEntropy p := by
  have hdiag : ∀ p : ℝ, Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] =
      Matrix.diagonal (fun i => (((![p, 1 - p] : Fin 2 → ℝ) i : ℝ) : ℂ)) := by
    intro p
    congr 1
    funext i
    fin_cases i <;> simp
  constructor
  · obtain ⟨hpsd, htr⟩ := hρ
    have hA := hpsd.1
    have hspec := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    have hsum := hA.trace_eq_sum_eigenvalues
    rw [htr, Fin.sum_univ_two] at hsum
    have hs : hA.eigenvalues 0 + hA.eigenvalues 1 = 1 := by
      have : ((1 : ℝ) : ℂ) = ((hA.eigenvalues 0 + hA.eigenvalues 1 : ℝ) : ℂ) := by
        push_cast; rw [hsum]; rfl
      exact_mod_cast this.symm
    have h0 := hpsd.eigenvalues_nonneg 0
    have h1 := hpsd.eigenvalues_nonneg 1
    refine ⟨hA.eigenvalues 0, ⟨hA.eigenvectorUnitary, hA.eigenvectorUnitary.2⟩, h0,
      by linarith, ?_⟩
    have hD : (RCLike.ofReal ∘ hA.eigenvalues : Fin 2 → ℂ) =
        ![(↑(hA.eigenvalues 0) : ℂ), 1 - ↑(hA.eigenvalues 0)] := by
      funext i
      fin_cases i
      · rfl
      · change ((hA.eigenvalues 1 : ℝ) : ℂ) = 1 - ((hA.eigenvalues 0 : ℝ) : ℂ)
        have : hA.eigenvalues 1 = 1 - hA.eigenvalues 0 := by linarith
        rw [this]; push_cast; ring
    conv_lhs => rw [hspec, hD]
  · intro p W hp0 hp1 hρW
    have hU1W : star (W : Mat2) * (W : Mat2) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
    have hU2W : (W : Mat2) * star (W : Mat2) = 1 := Matrix.mem_unitaryGroup_iff.mp W.2
    refine ⟨?_, ?_, ?_⟩
    · intro U i
      set M := star (W : Mat2) * (U : Mat2) with hM
      have hU1 : star (U : Mat2) * (U : Mat2) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
      have hU2 : (U : Mat2) * star (U : Mat2) = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
      have hsM : star M = star (U : Mat2) * (W : Mat2) := by rw [hM, star_mul, star_star]
      have hMM : star M * M = 1 := by
        rw [hsM, hM, Matrix.mul_assoc, ← Matrix.mul_assoc (W : Mat2), hU2W, Matrix.one_mul, hU1]
      have hMM' : M * star M = 1 := by
        rw [hsM, hM, Matrix.mul_assoc, ← Matrix.mul_assoc (U : Mat2), hU2, Matrix.one_mul, hU1W]
      have hconj : star (U : Mat2) * ρ * (U : Mat2) =
          star M * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * M := by
        rw [hρW, hsM, hM]; simp only [Matrix.mul_assoc]
      have hprob : ∀ j, prob U ρ j = ‖M 0 j‖ ^ 2 * p + ‖M 1 j‖ ^ 2 * (1 - p) := by
        intro j
        unfold prob
        rw [hconj]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.star_apply]
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          if_true, mul_ite, mul_zero, ite_mul, zero_mul, Fin.zero_eta, Fin.mk_one,
          show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, if_false, add_zero,
          zero_add]
        have e0 := conj_mul_self (M 0 j)
        have e1 := conj_mul_self (M 1 j)
        have h1 : star (M 0 j) * ↑p * M 0 j + star (M 1 j) * (1 - ↑p) * M 1 j =
            ↑p * (star (M 0 j) * M 0 j) + (1 - ↑p) * (star (M 1 j) * M 1 j) := by ring
        rw [h1, e0, e1]
        rw [show ((p : ℂ) * ((‖M 0 j‖ ^ 2 : ℝ) : ℂ) + (1 - (p : ℂ)) * ((‖M 1 j‖ ^ 2 : ℝ) : ℂ)) =
          ((‖M 0 j‖ ^ 2 * p + ‖M 1 j‖ ^ 2 * (1 - p) : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      have hcol : ∀ j, ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 = 1 := by
        intro j
        have := congrFun (congrFun hMM j) j
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
          conj_mul_self] at this
        exact_mod_cast this
      have hrow : ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 = 1 := by
        have := congrFun (congrFun hMM' 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq] at this
        rw [mul_comm (M 0 0), mul_comm (M 0 1), conj_mul_self, conj_mul_self] at this
        exact_mod_cast this
      have hq0 := hprob 0
      have hq1 := hprob 1
      have hc0 := hcol 0
      have hc1 := hcol 1
      unfold shannon fp WildeQIT.binaryEntropy
      rw [Fin.sum_univ_two]
      fin_cases i
      · simp only [Fin.zero_eta]
        have e1 : 1 - (‖M 0 0‖ ^ 2 * p + (1 - ‖M 0 0‖ ^ 2) * (1 - p)) = prob U ρ 1 := by
          rw [hq1]; nlinarith
        have e0 : ‖M 0 0‖ ^ 2 * p + (1 - ‖M 0 0‖ ^ 2) * (1 - p) = prob U ρ 0 := by
          rw [hq0]; nlinarith
        rw [e1, e0]; ring
      · simp only [Fin.mk_one]
        have e1 : 1 - (‖M 0 1‖ ^ 2 * p + (1 - ‖M 0 1‖ ^ 2) * (1 - p)) = prob U ρ 0 := by
          rw [hq0]; nlinarith
        have e0 : ‖M 0 1‖ ^ 2 * p + (1 - ‖M 0 1‖ ^ 2) * (1 - p) = prob U ρ 1 := by
          rw [hq1]; nlinarith
        rw [e1, e0]; ring
    · unfold purity
      rw [hρW]
      have : (W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2) *
          ((W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2)) =
          (W : Mat2) * (Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] *
            Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)]) * star (W : Mat2) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (W : Mat2)) (W : Mat2), hU1W, Matrix.one_mul]
      rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1W, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im]
      ring
    · rw [hρW, hdiag, entropy_conj, Fin.sum_univ_two]
      unfold WildeQIT.binaryEntropy
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
