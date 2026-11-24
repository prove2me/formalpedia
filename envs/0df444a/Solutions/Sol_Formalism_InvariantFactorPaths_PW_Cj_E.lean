-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Cj_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.346883+00:00
-- url     : https://prove2.me/submissions/e30b57ce-a880-4487-9c53-18699fe683ad

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_EE_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z j k : ι} (hz : z ∉ S) (hj : j ∈ S) (hk : k ∈ S) :
    Cj E S z j * E k z = E k z * Cj E S z j + (2 : K) • (E k z * E j z) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have hkz : k ≠ z := fun e => hz (e ▸ hk)
  have a1 : ∀ i ∈ S, E i z * E j i * E k z =
      E k z * (E i z * E j i) + (if i = k then E k z * E j z else 0) := by
    intro i hi
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    calc E i z * E j i * E k z = E i z * (E j i * E k z) := mul_assoc _ _ _
      _ = E i z * (E k z * E j i + (if i = k then E j z else 0)) := by
          rw [h.sw j i k z, if_neg (show ¬ z = j from fun e => hjz e.symm), sub_zero]
      _ = (E i z * E k z) * E j i + E i z * (if i = k then E j z else 0) := by rw [mul_add, mul_assoc]
      _ = E k z * (E i z * E j i) + (if i = k then E k z * E j z else 0) := by
          rw [EE_comm h hiz hkz, mul_assoc]
          split_ifs with hik
          · subst hik; rfl
          · rw [mul_zero]
  have a2 : E j z * E z z * E k z = E k z * (E j z * E z z) - E k z * E j z := by
    calc E j z * E z z * E k z = E j z * (E z z * E k z) := mul_assoc _ _ _
      _ = E j z * (E k z * E z z - E k z) := by
          rw [h.sw z z k z, if_neg (show ¬ z = k from fun e => hkz e.symm), if_pos (rfl : z = z), zero_sub,
            ← sub_eq_add_neg]
      _ = (E j z * E k z) * E z z - E j z * E k z := by rw [mul_sub, mul_assoc]
      _ = E k z * (E j z * E z z) - E k z * E j z := by rw [EE_comm h hjz hkz, mul_assoc]
  simp only [Cj, add_mul, sub_mul, Finset.sum_mul, smul_mul_assoc, mul_add, mul_sub, Finset.mul_sum,
    mul_smul_comm]
  rw [Finset.sum_congr rfl a1, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hk, a2, EE_comm h hjz hkz,
    two_smul]
  abel
end Formalism.InvariantFactorPaths.PW
