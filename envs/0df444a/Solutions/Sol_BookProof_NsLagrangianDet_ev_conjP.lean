-- Prove2me | solution 1 for BookProof.NsLagrangianDet.ev_conjP
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:26.66373+00:00
-- url     : https://prove2.me/submissions/3cc211a5-4330-4495-9b7a-4f2e8958c686

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.ev_conjP
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (y : DIdx K → ℝ) (p : MvPolynomial (DIdx K) ℂ) :
    ev y (conjP p) = (starRingEnd ℂ) (ev y p) := by

  rw [conjP, ev, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
