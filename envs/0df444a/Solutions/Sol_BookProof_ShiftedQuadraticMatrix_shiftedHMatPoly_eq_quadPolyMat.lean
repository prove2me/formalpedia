-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:01.535994+00:00
-- url     : https://prove2.me/submissions/9499f9e1-433a-47f7-8f53-e54992ca818b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_quadPolyMatT_apply_expand
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_foTPoly_apply_expand
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
theorem solution (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2)
    (f : MvPolynomial (Fin d) ℂ) :
    shiftedHMatPoly a k A b b' f
      = quadPolyMat A f + ((matShiftConst a k b b' : ℝ) : ℂ) • f := by

  classical
  have hS1 : ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
      = ∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h : ∑ q, ((A p q * k q : ℝ) : ℂ) = ((-(b' p) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, hk p]
    rw [← Finset.sum_smul, h]
  have hS2 : ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
      = ∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h : ∑ p, ((A p q * k p : ℝ) : ℂ) = ((-(b' q) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, ← hk q]
      exact congrArg _ (Finset.sum_congr rfl fun p _ => by rw [hsym p q])
    rw [← Finset.sum_smul, h]
  have hS3 : ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
      = ∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h : ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) = ((-(b p) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [← Finset.sum_div, ha p]
      ring
    rw [← Finset.sum_smul, h]
  have hS4 : ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
      = ∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h : ∑ p, ((A p q * a p / 4 : ℝ) : ℂ) = ((-(b q) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [← Finset.sum_div]
      have hrow : ∑ p, A p q * a p = -2 * b q := by
        rw [← ha q]
        exact Finset.sum_congr rfl fun p _ => by rw [hsym p q]
      rw [hrow]
      ring
    rw [← Finset.sum_smul, h]
  have hsum : ∑ p, ∑ q, A p q * (k p * k q + a p * a q / 4)
      = -(matShiftConst a k b b') := by
    have hstep : ∀ p : Fin d, ∑ q, A p q * (k p * k q + a p * a q / 4)
        = -(1/2) * (a p * b p) + -(1/2) * (b' p * k p) := by
      intro p
      have hexp : ∑ q, A p q * (k p * k q + a p * a q / 4)
          = k p * (∑ q, A p q * k q) + (a p * (∑ q, A p q * a q)) / 4 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      rw [hexp, hk p, ha p]
      ring
    rw [Finset.sum_congr rfl fun p _ => hstep p, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, matShiftConst]
    ring
  have hS5 : ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f
      = ((-(matShiftConst a k b b') : ℝ) : ℂ) • f := by
    simp only [← Finset.sum_smul]
    congr 1
    have hcast : (∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ))
        = ((∑ p, ∑ q, A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hsum]
  have hmom : (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
      + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
      + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add]
    norm_num
  have hx : (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
      + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
      + (∑ i, ((b i : ℝ) : ℂ) • (X i * f)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add]
    norm_num
  have hconst : ((-(matShiftConst a k b b') : ℝ) : ℂ) • f
      + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f
      = ((matShiftConst a k b b' : ℝ) : ℂ) • f := by
    rw [← add_smul, ← Complex.ofReal_add]
    congr 2
    rw [matShiftConst]
    have hsplit : ∑ i, (b i * a i + b' i * k i)
        = (∑ i, a i * b i) + ∑ i, b' i * k i := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    ring
  rw [shiftedHMatPoly, LinearMap.add_apply, quadPolyMatT_apply_expand, foTPoly_apply_expand,
    hS1, hS2, hS3, hS4, hS5]
  rw [show quadPolyMat A f
        + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
        + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
        + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
        + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
        + ((-(matShiftConst a k b b') : ℝ) : ℂ) • f
        + ((∑ i, ((b i : ℝ) : ℂ) • (X i * f)) + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f)
            + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f)
      = quadPolyMat A f
        + ((∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
            + (∑ p, ((-(b' p) / 2 : ℝ) : ℂ) • momPoly p f)
            + (∑ i, ((b' i : ℝ) : ℂ) • momPoly i f))
        + ((∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
            + (∑ p, ((-(b p) / 2 : ℝ) : ℂ) • (X p * f))
            + (∑ i, ((b i : ℝ) : ℂ) • (X i * f)))
        + (((-(matShiftConst a k b b') : ℝ) : ℂ) • f
            + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f) from by abel]
  rw [hmom, hx, hconst]
  abel
