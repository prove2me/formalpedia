-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.ccr_phi_pi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:33:35.235828+00:00
-- url     : https://prove2.me/submissions/5934b721-14ad-4f82-acc4-935950a6024e

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.ccr_phi_pi
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (p : P) :
    (fieldOp 0) (momOp 0 p) - (momOp 0) (fieldOp 0 p) = Complex.I • p := by

  change X 0 * ((-Complex.I) • pderiv 0 p)
      - (-Complex.I) • pderiv 0 (X 0 * p) = Complex.I • p
  rw [pderiv_mul]
  simp
