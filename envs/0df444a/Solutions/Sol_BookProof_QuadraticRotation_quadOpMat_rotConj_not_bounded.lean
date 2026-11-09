-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_rotConj_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:08:18.34943+00:00
-- url     : https://prove2.me/submissions/4f23b0ef-2440-4d95-800b-e33aac822b35

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_rotConj_not_bounded
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_orthonormal_rotHermiteLp
import Theorems.Thm_BookProof_QuadraticRotation_rotHermiteLp_mem_core
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotHermiteLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadSymbol_single
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) {i : Fin d} (hci : c i ≠ 0) :
    ¬ ∃ K : ℝ, ∀ f : polyGaussCore (d := d),
        ‖quadOpMat (rotConj O c) f‖ ≤ K * ‖(f : L2d d)‖ := by

  classical
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + |∑ j, c j * (1/2)|) / |c i|)
  set a : Fin d →₀ ℕ := Finsupp.single i n with ha
  have hnorm : ‖rotHermiteLp (d := d) O a‖ = 1 := (orthonormal_rotHermiteLp hO).norm_eq_one a
  have h := hK ⟨rotHermiteLp O a, rotHermiteLp_mem_core O a⟩
  rw [quadOpMat_rotHermiteLp hO c a (rotHermiteLp_mem_core O a), norm_smul] at h
  simp only [hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have hci' : 0 < |c i| := abs_pos.mpr hci
  have hlow : |c i| * (n : ℝ) - |∑ j, c j * (1/2)| ≤ |quadSymbol c a| := by
    have htri : |c i * (n : ℝ)|
        ≤ |c i * (n : ℝ) + ∑ j, c j * (1/2)| + |∑ j, c j * (1/2)| := by
      have h1 : |c i * (n : ℝ) + ∑ j, c j * (1/2)| + |-(∑ j, c j * (1/2))|
          ≥ |c i * (n : ℝ) + ∑ j, c j * (1/2) + -(∑ j, c j * (1/2))| := abs_add_le _ _
      simpa using h1
    have habs : |c i * (n : ℝ)| = |c i| * (n : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    rw [ha, quadSymbol_single]
    linarith [htri, habs.symm.le, habs.le]
  have hbig : K < |c i| * (n : ℝ) - |∑ j, c j * (1/2)| := by
    have hmul : (K + |∑ j, c j * (1/2)|) < |c i| * (n : ℝ) := by
      rw [div_lt_iff₀ hci'] at hn
      linarith [hn]
    linarith
  linarith [h, hlow, hbig]
