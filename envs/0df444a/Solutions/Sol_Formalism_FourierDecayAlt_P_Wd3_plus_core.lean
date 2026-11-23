-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.plus_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:44.132648+00:00
-- url     : https://prove2.me/submissions/58052052-910f-4c30-8365-e5172c0dcbbd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul_eU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (h : ∀ i r j s, D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hM' : ∀ i j, FreeOf a (M i j) := hM
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, D • (eU a r s * (M i j * N r s)) - eU a r s * (M r j * N i s) =
      D • (eU a r s * (N r s * M i j)) - eU a r s * (N r j * M i s) := fun r s => by
    have := congrArg (eU a r s * ·) (h i r j s)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : (((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (M i j * ins a N) - ∑ k, eU a k i * M k j * ins a N := by
    rw [sub_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    rfl
  have hR : ((d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (ins a N * M i j) - ∑ k, ins a N * (M i k * eU a j k) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_apply, Matrix.smul_apply, d0,
      Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, mul_assoc]
    rfl
  rw [hL, hR, mul_ins a _ N (hM' i j), ins_mul,
    Finset.sum_congr rfl fun k _ => eU_mul_ins a k i (M k j) N (hM' k j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU a j k (M i k) N (hM' i k) hN,
    Finset.sum_comm (f := fun k r => eU a r k * (N r j * M i k)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s
end Formalism.FourierDecayAlt.P.Wd3
