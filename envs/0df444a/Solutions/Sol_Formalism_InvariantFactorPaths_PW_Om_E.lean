-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:53.719798+00:00
-- url     : https://prove2.me/submissions/1e0f2bc2-63f9-4aed-a16e-c17a0e83eceb

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_EE_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Cj_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_rec

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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) (q : ℕ) :
    E j z * Om E S z (q + 1) = Om E S z (q + 1) * E j z +
      ((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z)) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  induction q with
  | zero =>
    rw [Om_rec h hz hj 0]
    congr 1
    simp [Om]
  | succ q ih =>
    have hA : E j z * Om E S z (q + 1) - Om E S z (q + 1) * E j z =
        ((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z)) := sub_eq_iff_eq_add'.mpr ih
    have hX : ∀ i ∈ S, (Cj E S z j + (q : K) • E j z) * E i z =
        E i z * (Cj E S z j + (q : K) • E j z + (2 : K) • E j z) := by
      intro i hi
      have hiz : i ≠ z := fun e => hz (e ▸ hi)
      rw [add_mul, Cj_E h hz hj hi, smul_mul_assoc, EE_comm h hjz hiz, mul_add, mul_add, mul_smul_comm,
        mul_smul_comm]
      abel
    have hs : ∑ i ∈ S, E z i * (((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z))) * E i z =
        ((q : K) + 1) • (Om E S z (q + 1) * (Cj E S z j + (q : K) • E j z + (2 : K) • E j z)) := by
      simp only [Om, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [mul_assoc]
      rw [hX i hi]
    rw [Om_rec h hz hj (q + 1), hA, hs]
    congr 1
    push_cast
    simp only [mul_add, mul_smul_comm]
    module
end Formalism.InvariantFactorPaths.PW
