-- Prove2me | solution 1 for BookProof.NsLagrangianDet.det_rows_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:20.059191+00:00
-- url     : https://prove2.me/submissions/0e03fc2d-e95f-45a4-b04e-6a32786b362f

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.det_rows_sum
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R]
    (v : n → ι → n → R) :
    (Matrix.of fun r c => ∑ o, v r o c).det
      = ∑ τ : n → ι, (Matrix.of fun r c => v r (τ r) c).det := by

  have h := (Matrix.detRowAlternating (n := n) (R := R)).toMultilinearMap.map_sum
    (fun r o => v r o)
  have e1 : (Matrix.of fun r c => ∑ o, v r o c) = fun r => ∑ o, v r o := by
    ext r c; simp [Finset.sum_apply]
  rw [e1]
  exact h
