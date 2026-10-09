-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.eulerOp_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:34:40.392872+00:00
-- url     : https://prove2.me/submissions/2ae1b4c2-497b-4c4e-9c20-5d3bc0421380

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.eulerOp_X
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 2) : eulerOp (X j) = X j := by

  fin_cases j <;>
    simp [eulerOp_apply,
      pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
