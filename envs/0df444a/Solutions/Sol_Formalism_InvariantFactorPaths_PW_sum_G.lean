-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.sum_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:02.169169+00:00
-- url     : https://prove2.me/submissions/0c239cbf-02af-45c4-937d-2563e257f53f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw

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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) :
    ∑ i ∈ S, (E j i - (if i = j then E z z else 0)) * E i z = Cj E S z j := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have h1 : ∀ i ∈ S, E j i * E i z = E i z * E j i + E j z := by
    intro i _
    rw [h.sw j i i z, if_pos (rfl : i = i), if_neg (show ¬ z = j from fun e => hjz e.symm), sub_zero]
  have h2 : E z z * E j z = E j z * E z z - E j z := by
    rw [h.sw z z j z, if_neg (show ¬ z = j from fun e => hjz e.symm), if_pos (rfl : z = z), zero_sub,
      ← sub_eq_add_neg]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', if_pos hj, h2, Cj, Finset.sum_const, add_smul, one_smul]
  rw [← Nat.cast_smul_eq_nsmul K]
  abel
end Formalism.InvariantFactorPaths.PW
