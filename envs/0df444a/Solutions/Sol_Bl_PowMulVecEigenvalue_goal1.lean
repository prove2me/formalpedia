-- Prove2me | solution 1 for Bl.PowMulVecEigenvalue.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:04.439461+00:00
-- url     : https://prove2.me/submissions/04c4bd8d-3a7e-4ed0-9b0a-6362ca0ac911

import Mathlib
import Definitions.Def_Lemmata_PowMulVecEigenvalue_PowMulVecEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.PowMulVecEigenvalue
private lemma pow_mulVec_eig {S : Type u_1} [CommRing S] {n : Type u_2} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (h : Q.mulVec v = μ • v) (k : ℕ) :
    (Q ^ k).mulVec v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
end Bl.PowMulVecEigenvalue
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.PowMulVecEigenvalue
namespace Bl.PowMulVecEigenvalue
theorem _root_.solution :
  ∀ {S : Type u_1} [inst : CommRing.{u_1} S] {n : Type u_2} [inst_1 : Fintype.{u_2} n] [inst_2 : DecidableEq.{u_2 + 1} n]
  (Q : Matrix.{u_2, u_2, u_1} n n S) (μ : S) (v : n → S),
  Eq.{max (u_1 + 1) (u_2 + 1)} (Matrix.mulVec.{u_1, u_2, u_2} Q v) (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} μ v) →
    ∀ (p : Polynomial.{0} Int),
      Eq.{max (u_1 + 1) (u_2 + 1)}
        (Matrix.mulVec.{u_1, u_2, u_2}
          (DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) 1, 1, max (u_1 + 1) (u_2 + 1)}
            (Polynomial.aeval.{0, max u_1 u_2} Q) p)
          v)
        (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2}
          (DFunLike.coe.{max (u_1 + 1) 1, 1, u_1 + 1} (Polynomial.aeval.{0, u_1} μ) p) v) := by
  intro S _ n _ _ Q μ v h p
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, pow_mulVec_eig Q μ v h i, smul_assoc]
end Bl.PowMulVecEigenvalue
