-- Prove2me | solution 1 for Bl.PowMulVecEigen.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:02.064344+00:00
-- url     : https://prove2.me/submissions/39b4d54c-c9d5-406a-b430-fe14a1c703cc

import Mathlib
import Definitions.Def_Lemmata_PowMulVecEigen_PowMulVecEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPowerSeries
namespace Bl.PowMulVecEigen
variable {C : Type} [Field C]
private lemma pow_mulVec_eig {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (k : ℕ) :
    Matrix.mulVec (A ^ k) w = lam ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]
end Bl.PowMulVecEigen
end

set_option autoImplicit false
open MvPowerSeries
open Bl Bl.PowMulVecEigen
variable {C : Type} [Field C]
namespace Bl.PowMulVecEigen
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, pow_mulVec_eig A w lam h k, Polynomial.eval_monomial, smul_smul]
end Bl.PowMulVecEigen
