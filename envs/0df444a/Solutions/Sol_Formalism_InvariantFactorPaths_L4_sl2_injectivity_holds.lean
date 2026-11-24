-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sl2_injectivity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:02.72502+00:00
-- url     : https://prove2.me/submissions/32183b7f-8287-4975-9166-0c5bb577cd3a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_raise_pow_succ_lower_apply_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_eq_zero_of_lower_zero_of_raise_pow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : Sl2Injective := by
  intro k V _ _ _ _ e f h he hf hef u μ j hu hex hj h0
  obtain ⟨s, hs⟩ := hex
  induction s generalizing u μ j with
  | zero => simpa using hs
  | succ s ih =>
    have hfu : f u = 0 := by
      apply ih (f u) (μ - 2) (j + 1)
      · have h1 := hf u
        rw [hu, map_smul, sub_eq_iff_eq_add] at h1
        rw [h1]
        push_cast
        rw [sub_smul]
        abel
      · omega
      · rw [sl2_raise_pow_succ_lower_apply_eq he hef hu j, pow_succ', Module.End.mul_apply, h0]
        simp
      · rw [pow_succ, Module.End.mul_apply] at hs
        exact hs
    exact sl2_eq_zero_of_lower_zero_of_raise_pow_zero he hef hu hfu j hj h0
end Formalism.InvariantFactorPaths.L4
