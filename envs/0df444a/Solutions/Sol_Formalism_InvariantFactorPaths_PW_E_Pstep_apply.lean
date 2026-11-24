-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.E_Pstep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:55.492995+00:00
-- url     : https://prove2.me/submissions/9ccf345e-4f94-44e4-a85a-ccca89247de8

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_cc_rec
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_cc_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_E_Om_apply

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
theorem _root_.solution [CharZero K] (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (n : ℕ) :
    E j z (Pstep E S z n u) = cc K S.card n • Om E S z n (E j z u) := by
  induction n with
  | zero =>
    rw [Pstep_eq]
    simp [Om, cc_zero]
  | succ n ih =>
    rw [Pstep_eq, Finset.sum_range_succ, ← Pstep_eq]
    simp only [LinearMap.add_apply, map_add, ih, LinearMap.smul_apply, map_smul,
      E_Om_apply h hz hj hS hzz n]
    rw [eq_neg_of_add_eq_zero_left (cc_rec (K := K) S.card n)]
    module
end Formalism.InvariantFactorPaths.PW
