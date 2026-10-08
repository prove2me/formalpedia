-- Prove2me | solution 1 for BookProof.BookBrstYangMills.rsmul_eq_csmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:47:31.911759+00:00
-- url     : https://prove2.me/submissions/bdad3609-9c41-43cf-b0d7-69e9e4569edf

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.rsmul_eq_csmul
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (r : ℝ) (T : Module.End ℂ (BookState N)) :
    r • T = ((r : ℝ) : ℂ) • T := by

  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.smul_apply]
  exact (algebraMap_smul ℂ r (T x)).symm
