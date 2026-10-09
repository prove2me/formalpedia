-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.commForm_sqSumOp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:34:54.957982+00:00
-- url     : https://prove2.me/submissions/9197b0e0-dbbe-4406-a33d-80eca081fd71

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.commForm_sqSumOp_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_eval_gradPoly
import Theorems.Thm_BookProof_SqSumFarisLavine_cpoly_gradPoly
import Theorems.Thm_BookProof_SqSumFarisLavine_commPoly_eq
import Theorems.Thm_BookProof_SqSumFarisLavine_commForm_eq_im
import Theorems.Thm_BookProof_SqSumFarisLavine_core_eq_pgLp
import Theorems.Thm_BookProof_SqSumFarisLavine_abs_im_gaussInt_le
import Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_self
import Theorems.Thm_BookProof_GaussCoreQuadBounds_quadForm_harm_eq
import Theorems.Thm_BookProof_GaussCoreQuadBounds_sum_norm_sq_mul_le_of_pointwise
import Definitions.Def_ChapterHermiteProductCore
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_X
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_mul
open BookProof.SqSumFarisLavine




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km M : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hM0 : 0 ≤ M)
    (hM : ∀ x : Vd D, ∑ k : Fin D, (gradFun v k x) ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2)
    (u : polyGaussCore (d := D)) :
    |commForm (sqSumOp kappa v) harmCore u| ≤ (km / 2 + 2 * M) * quadForm harmCore u := by

  obtain ⟨p, hu⟩ := core_eq_pgLp u
  subst hu
  rw [commForm_eq_im, quadForm_harm_eq]
  set a : Fin D → ℝ := fun j => ‖pgLp (coreD j p)‖ with hadef
  set b : Fin D → ℝ := fun j => ‖pgLp (X j * p)‖ with hbdef
  set g : Fin D → ℝ := fun k => ‖pgLp (gradPoly v k * p)‖ with hgdef
  -- the expansion of the pairing against the commutator
  have hZ : gaussInt (cpoly p * commPoly kappa v p)
      = ((commConst kappa v : ℝ) : ℂ) * ((‖pgLp p‖ ^ 2 : ℝ) : ℂ)
        + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ)
            * gaussInt (cpoly (X j * p) * coreD j p))
        + (2 : ℂ) * ∑ k : Fin D, gaussInt (cpoly (gradPoly v k * p) * coreD k p) := by
    have hswapX : ∀ j : Fin D,
        cpoly p * (X j * coreD j p) = cpoly (X j * p) * coreD j p := by
      intro j
      rw [cpoly_mul, cpoly_X]
      ring
    have hswapG : ∀ k : Fin D,
        cpoly p * (gradPoly v k * coreD k p) = cpoly (gradPoly v k * p) * coreD k p := by
      intro k
      rw [cpoly_mul, cpoly_gradPoly]
      ring
    rw [commPoly_eq, mul_add, mul_add, gaussInt_add, gaussInt_add]
    congr 1
    · congr 1
      · rw [mul_smul_comm, gaussInt_smul, BookProof.GaussCoreQuadBounds.gaussInt_self]
      · rw [Finset.mul_sum, gaussInt_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, gaussInt_smul, hswapX j]
    · rw [mul_smul_comm, gaussInt_smul, Finset.mul_sum, gaussInt_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hswapG k]
  have him : (gaussInt (cpoly p * commPoly kappa v p)).im
      = (∑ j : Fin D, (-(kappa j) / 2) * (gaussInt (cpoly (X j * p) * coreD j p)).im)
        + 2 * ∑ k : Fin D, (gaussInt (cpoly (gradPoly v k * p) * coreD k p)).im := by
    rw [hZ]
    simp only [Complex.add_im, Complex.im_sum, Complex.im_ofReal_mul, Complex.ofReal_im,
      mul_zero, zero_add]
    congr 1
    rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul, Complex.im_sum]
  -- the two families of bounds
  have hT : ∀ j : Fin D, |(gaussInt (cpoly (X j * p) * coreD j p)).im| ≤ b j * a j :=
    fun j => abs_im_gaussInt_le _ _
  have hS : ∀ k : Fin D, |(gaussInt (cpoly (gradPoly v k * p) * coreD k p)).im| ≤ g k * a k :=
    fun k => abs_im_gaussInt_le _ _
  have hg2 : ∑ k : Fin D, (g k) ^ 2 ≤ M ^ 2 * ∑ k : Fin D, (b k) ^ 2 := by
    refine sum_norm_sq_mul_le_of_pointwise (fun x => ?_) p
    have hx := hM x
    have hgrad : ∀ k : Fin D,
        ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gradPoly v k)‖ ^ 2
          = (gradFun v k x) ^ 2 := by
      intro k
      rw [eval_gradPoly, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hX : ∀ k : Fin D,
        ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (X k : MvPolynomial (Fin D) ℂ)‖ ^ 2
          = (x k) ^ 2 := by
      intro k
      rw [MvPolynomial.eval_X, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [hgrad, hX]
    rw [← norm_sq_eq_sum x]
    exact hx
  -- the harmonic-oscillator quadratic form
  have hquad : ∀ j : Fin D, b j * a j ≤ (a j) ^ 2 + (b j) ^ 2 / 4 := by
    intro j
    nlinarith [sq_nonneg (a j - b j / 2)]
  have hAnn : ∀ j : Fin D, 0 ≤ a j := fun j => norm_nonneg _
  have hBnn : ∀ j : Fin D, 0 ≤ b j := fun j => norm_nonneg _
  have hGnn : ∀ j : Fin D, 0 ≤ g j := fun j => norm_nonneg _
  -- bound of the signature term
  have hbound1 : |∑ j : Fin D, (-(kappa j) / 2) * (gaussInt (cpoly (X j * p) * coreD j p)).im|
      ≤ km / 2 * ∑ j : Fin D, ((a j) ^ 2 + (b j) ^ 2 / 4) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    have habs : |(-(kappa j) / 2)| ≤ km / 2 := by
      rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      linarith [hk j]
    calc |(-(kappa j) / 2)| * |(gaussInt (cpoly (X j * p) * coreD j p)).im|
        ≤ (km / 2) * (b j * a j) := by
          refine mul_le_mul habs (hT j) (abs_nonneg _) (by linarith)
      _ ≤ km / 2 * ((a j) ^ 2 + (b j) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left (hquad j) (by linarith)
  -- bound of the torsion term
  have hsum2 : ∑ k : Fin D, (g k * a k) ≤ M * ∑ j : Fin D, ((a j) ^ 2 + (b j) ^ 2 / 4) := by
    rcases eq_or_lt_of_le hM0 with hM0' | hMpos
    · have hgz : ∀ k : Fin D, g k = 0 := by
        have hle : ∑ k : Fin D, (g k) ^ 2 ≤ 0 := by
          rw [← hM0'] at hg2
          simpa using hg2
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k (_ : k ∈ Finset.univ) => sq_nonneg (g k))).mp (le_antisymm hle
            (Finset.sum_nonneg fun k _ => sq_nonneg (g k)))
        intro k
        have := hall k (Finset.mem_univ k)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [hgz, zero_mul, Finset.sum_const_zero, ← hM0', zero_mul]
      exact le_refl 0
    · have h2M : (0 : ℝ) < 2 * M := by linarith
      have hyoung : ∀ k : Fin D, 2 * (g k * a k) ≤ (g k) ^ 2 / (2 * M) + 2 * M * (a k) ^ 2 := by
        intro k
        rw [← sub_nonneg]
        have key : (g k) ^ 2 / (2 * M) + 2 * M * (a k) ^ 2 - 2 * (g k * a k)
            = (g k - 2 * M * a k) ^ 2 / (2 * M) := by
          field_simp
          ring
        rw [key]
        positivity
      have hstep : 2 * ∑ k : Fin D, (g k * a k)
          ≤ (∑ k : Fin D, (g k) ^ 2) / (2 * M) + 2 * M * ∑ k : Fin D, (a k) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => hyoung k
      have hdiv : (∑ k : Fin D, (g k) ^ 2) / (2 * M) ≤ (M / 2) * ∑ k : Fin D, (b k) ^ 2 := by
        rw [div_le_iff₀ h2M]
        nlinarith [hg2]
      have hexp : ∑ j : Fin D, ((a j) ^ 2 + (b j) ^ 2 / 4)
          = (∑ j : Fin D, (a j) ^ 2) + (∑ j : Fin D, (b j) ^ 2) / 4 := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
      rw [hexp]
      nlinarith [hstep, hdiv]
  have hbound2 : |2 * ∑ k : Fin D, (gaussInt (cpoly (gradPoly v k * p) * coreD k p)).im|
      ≤ 2 * M * ∑ j : Fin D, ((a j) ^ 2 + (b j) ^ 2 / 4) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    have h1 : |∑ k : Fin D, (gaussInt (cpoly (gradPoly v k * p) * coreD k p)).im|
        ≤ ∑ k : Fin D, (g k * a k) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => hS k)
    linarith [hsum2]
  rw [abs_neg, him]
  refine le_trans (abs_add_le _ _) ?_
  nlinarith [hbound1, hbound2]
