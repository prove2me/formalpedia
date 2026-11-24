-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.shifted_flip_position_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:22.533263+00:00
-- url     : https://prove2.me/submissions/47765d1c-0bc1-422d-b4bf-fe00513d1323

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_mul_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_unit_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_mul_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * lift0 M * d0 (ins a (lift0 N)) =
      d0 (ins a (lift0 N)) * lift0 M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have L : ∀ i k, ((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * lift0 M * d0 (ins a (lift0 N)) : M2 (SlopeTestRemainingChoices S A)) i k =
      ∑ r, ∑ s, eU a r s * io (D • (M i k * N r s) - M r k * N i s) := by
    intro i k
    unfold d0
    rw [Matrix.mul_diagonal, sub_mul, Matrix.sub_apply, smul_mul_assoc, one_mul, Matrix.smul_apply,
      sub_mul, smul_mul_assoc, Matrix.mul_apply]
    simp only [io_sub, io_smul, mul_sub, Finset.sum_sub_distrib, mul_smul_comm, ← Finset.smul_sum]
    congr 1
    · congr 1
      exact io_mul_ins a (M i k) N
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact unit_mul_ins a r i (M r k) N
  have Rr : ∀ i k, (d0 (ins a (lift0 N)) * lift0 M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A)) i k =
      ∑ r, ∑ s, eU a r s * io (D • (N r s * M i k) - N r k * M i s) := by
    intro i k
    unfold d0
    rw [mul_assoc, Matrix.diagonal_mul, mul_sub, Matrix.sub_apply, mul_smul_comm, mul_one, Matrix.smul_apply,
      mul_sub, mul_smul_comm, Matrix.mul_apply]
    simp only [io_sub, io_smul, mul_sub, Finset.sum_sub_distrib, mul_smul_comm, ← Finset.smul_sum]
    congr 1
    · congr 1
      exact ins_mul_io a (M i k) N
    · rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      exact ins_mul_unit a k s (M i s) N
  ext1 i k
  rw [L, Rr]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [h i k r s]
end Formalism.FourierDecayAlt.P.Wd6
