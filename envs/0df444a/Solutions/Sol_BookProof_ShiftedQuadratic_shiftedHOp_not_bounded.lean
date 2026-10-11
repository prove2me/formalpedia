-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_not_bounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:17.757142+00:00
-- url     : https://prove2.me/submissions/cee391f4-c646-4544-86ba-7c0f50cac763
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_not_bounded
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_hermiteTLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadSymbol_single
import Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedHermiteCore_orthonormal_hermiteTLp
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {i : Fin d} :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (shiftVec c b) (boostVec c b'),
        ‖shiftedHOp (shiftVec c b) (boostVec c b') c b b' f‖ ≤ C * ‖(f : L2d d)‖ := by

  classical
  rintro ⟨C, hC⟩
  set S : ℝ := ∑ j, c j * (1/2) + shiftConst c b b' with hS
  set K : ℝ := |S| with hK
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + K) / |c i|)
  set α : Fin d →₀ ℕ := Finsupp.single i n with hα
  have hnorm : ‖hermiteTLp (d := d) (shiftVec c b) (boostVec c b') α‖ = 1 :=
    (orthonormal_hermiteTLp _ _).norm_eq_one α
  have h := hC ⟨hermiteTLp (shiftVec c b) (boostVec c b') α,
    hermiteTLp_mem_coreT (shiftVec c b) (boostVec c b') α⟩
  rw [shiftedHOp_hermiteTLp c b b' hc α
    (hermiteTLp_mem_coreT (shiftVec c b) (boostVec c b') α), norm_smul] at h
  simp only [hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have hci' : 0 < |c i| := abs_pos.mpr (hc i)
  have hsym : quadSymbol c α + shiftConst c b b' = c i * (n : ℝ) + S := by
    rw [hα, quadSymbol_single, hS]
    ring
  have hlow : |c i| * (n : ℝ) - K ≤ |quadSymbol c α + shiftConst c b b'| := by
    have htri : |c i * (n : ℝ)| ≤ |c i * (n : ℝ) + S| + K := by
      have h1 := abs_add_le (c i * (n : ℝ) + S) (-S)
      rw [hK]
      simpa using h1
    have habs : |c i * (n : ℝ)| = |c i| * (n : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    rw [hsym]
    linarith [htri, habs.symm.le, habs.le]
  have hbig : C < |c i| * (n : ℝ) - K := by
    have hmul : (C + K) < |c i| * (n : ℝ) := by
      rw [div_lt_iff₀ hci'] at hn
      linarith [hn]
    linarith
  linarith [h, hlow, hbig]
