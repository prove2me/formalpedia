-- Prove2me | solution 1 for BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:33:22.218+00:00
-- url     : https://prove2.me/submissions/4cbd9685-54bf-4ef0-8817-6cb01a736f63

-- Generated from ChapterGaugeMechanicsCharge.lean — solution of BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge





open MvPolynomial

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 2) (p : P) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by

  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, hp]
      split_ifs with h1 h2 h2 <;> (simp; try ring)
