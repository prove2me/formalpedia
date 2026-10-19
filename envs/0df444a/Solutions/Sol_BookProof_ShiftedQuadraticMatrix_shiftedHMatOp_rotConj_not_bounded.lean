-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:44:49.26443+00:00
-- url     : https://prove2.me/submissions/3ca534b4-ded8-40e6-8eee-0c837c18f4e6

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_not_bounded
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_orthonormal_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_hermiteTRLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadSymbol_single
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    {i : Fin d} (hci : c i ≠ 0) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT a k,
        ‖shiftedHMatOp a k (rotConj O c) b b' f‖ ≤ C * ‖(f : L2d d)‖ := by

  classical
  rintro ⟨C, hC⟩
  set S : ℝ := ∑ j, c j * (1/2) + matShiftConst a k b b' with hS
  set K : ℝ := |S| with hK
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + K) / |c i|)
  set α : Fin d →₀ ℕ := Finsupp.single i n with hα
  have hnorm : ‖hermiteTRLp (d := d) O a k α‖ = 1 :=
    (orthonormal_hermiteTRLp hO a k).norm_eq_one α
  have h := hC ⟨hermiteTRLp O a k α, hermiteTRLp_mem_coreT O a k α⟩
  rw [shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α
    (hermiteTRLp_mem_coreT O a k α), norm_smul] at h
  simp only [hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have hci' : 0 < |c i| := abs_pos.mpr hci
  have hsymb : quadSymbol c α + matShiftConst a k b b' = c i * (n : ℝ) + S := by
    rw [hα, quadSymbol_single, hS]
    ring
  have hlow : |c i| * (n : ℝ) - K ≤ |quadSymbol c α + matShiftConst a k b b'| := by
    have htri : |c i * (n : ℝ)| ≤ |c i * (n : ℝ) + S| + K := by
      have h1 := abs_add_le (c i * (n : ℝ) + S) (-S)
      rw [hK]
      simpa using h1
    have habs : |c i * (n : ℝ)| = |c i| * (n : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    rw [hsymb]
    linarith [htri, habs.symm.le, habs.le]
  have hbig : C < |c i| * (n : ℝ) - K := by
    have hmul : (C + K) < |c i| * (n : ℝ) := by
      rw [div_lt_iff₀ hci'] at hn
      linarith [hn]
    linarith
  linarith [h, hlow, hbig]
