-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:54.718832+00:00
-- url     : https://prove2.me/submissions/7f5da062-e993-4675-b617-efe738fbc344

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
open BookProof.ShiftedQuadraticDegenerate




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) {a w : Fin d → ℝ} (ha : ∀ i, ∑ j, A i j * a j = w i)
    {v : Fin d → ℝ} (hv : ∀ i, ∑ j, A i j * v j = 0) :
    ∑ i, w i * v i = 0 := by
  have h1 : ∑ i, w i * v i = ∑ i, ∑ j, A i j * a j * v i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, Finset.sum_mul]
  have h2 : ∑ i, ∑ j, A i j * a j * v i = ∑ j, a j * ∑ i, A j i * v i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hsym i j]; ring
  rw [h1, h2]
  exact Finset.sum_eq_zero fun j _ => by rw [hv j, mul_zero]
