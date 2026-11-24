-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:49.644802+00:00
-- url     : https://prove2.me/submissions/8bb338e1-b86d-4d3f-99bc-12f34267fcd4

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_der3
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_comm_S
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_diag_comm_omega
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_EE_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_sum_G

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
      (∑ i ∈ S, E z i * (E j z * Om E S z q - Om E S z q * E j z) * E i z + Om E S z q * Cj E S z j) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have key : ∀ i ∈ S, E j z * (E z i * Om E S z q * E i z) = (E z i * Om E S z q * E i z) * E j z +
      (E z i * (E j z * Om E S z q - Om E S z q * E j z) * E i z +
        Om E S z q * ((E j i - (if i = j then E z z else 0)) * E i z)) := by
    intro i hi
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    rw [der3 _ _ _ _ _ (E j z * Om E S z q - Om E S z q * E j z) 0 (h.sw j z z i) (by abel)
      (by rw [EE_comm h hjz hiz, add_zero]), if_pos rfl]
    have hc : (E j i - (if i = j then E z z else 0)) * Om E S z q =
        Om E S z q * (E j i - (if i = j then E z z else 0)) := by
      rw [sub_mul, mul_sub, Om_comm_S h hz hj hi]
      split_ifs
      · rw [diag_comm_omega h hz]
      · simp
    rw [hc, mul_zero, add_zero, mul_assoc (Om E S z q)]
    abel
  simp only [Om, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_G h hz hj]
end Formalism.InvariantFactorPaths.PW
